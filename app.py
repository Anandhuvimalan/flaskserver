from flask import Flask, render_template, request, jsonify, send_file, session
import os
import csv
import json
import time
import threading
import uuid
import requests
import re
import h3
import multiprocessing as mp
from collections import defaultdict, deque
from functools import lru_cache
from urllib.parse import urlparse, urljoin, urlunparse
from bs4 import BeautifulSoup
from typing import Set, List, Dict, Tuple, Optional, Any, Union
from werkzeug.utils import secure_filename
import tldextract

app = Flask(__name__)
app.secret_key = os.urandom(24)
app.config['UPLOAD_FOLDER'] = 'uploads'
app.config['OUTPUT_FOLDER'] = 'outputs'
app.config['MAX_CONTENT_LENGTH'] = 16 * 1024 * 1024  # 16MB max upload

# Create necessary directories
os.makedirs(app.config['UPLOAD_FOLDER'], exist_ok=True)
os.makedirs(app.config['OUTPUT_FOLDER'], exist_ok=True)

# Global process tracking
processes = {}

# ------------------------------
# Constants and Configuration
# ------------------------------
EMAIL_REGEX = re.compile(r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b', re.IGNORECASE)
INVALID_TLDS = {
    'png', 'jpg', 'jpeg', 'gif', 'svg', 'webp', 'bmp', 'ico', 'tiff',
    'css', 'js', 'pdf', 'doc', 'docx', 'xls', 'xlsx', 'ppt', 'pptx', 'zip'
}

# API configuration
DETAIL_FIELDS = (
    # Basic
    "address_components,adr_address,business_status,formatted_address,geometry,icon,icon_mask_base_uri,"
    "icon_background_color,name,permanently_closed,photos,place_id,plus_code,types,url,utc_offset,vicinity,"
    "wheelchair_accessible_entrance,"
    # Contact
    "current_opening_hours,formatted_phone_number,international_phone_number,opening_hours,secondary_opening_hours,website,"
    # Atmosphere
    "curbside_pickup,delivery,dine_in,editorial_summary,price_level,rating,reservable,reviews,serves_beer,"
    "serves_breakfast,serves_brunch,serves_dinner,serves_lunch,serves_vegetarian_food,serves_wine,takeout,user_ratings_total"
)

# CSV columns
COLUMNS = [
    # Basic
    "address_components", "adr_address", "business_status", "formatted_address", "geometry",
    "icon", "icon_mask_base_uri", "icon_background_color", "name", "permanently_closed", "photos",
    "place_id", "plus_code", "types", "url", "utc_offset", "vicinity", "wheelchair_accessible_entrance",
    # Contact
    "current_opening_hours", "formatted_phone_number", "international_phone_number",
    "opening_hours", "secondary_opening_hours", "website",
    # Atmosphere
    "curbside_pickup", "delivery", "dine_in", "editorial_summary", "price_level", "rating",
    "reservable", "reviews", "serves_beer", "serves_breakfast", "serves_brunch", "serves_dinner",
    "serves_lunch", "serves_vegetarian_food", "serves_wine", "takeout", "user_ratings_total",
    # Emails field
    "emails", 
    # Location info
    "h3_index", "search_lat", "search_lng", "city"
]

# ------------------------------
# Email Extraction Functions
# ------------------------------
@lru_cache(maxsize=1024)
def is_hex_like_local_part(email: str, min_length: int = 16) -> bool:
    """
    Check if the local part of an email (before the @) is composed solely of hex digits
    and is at least min_length long. Uses LRU cache for performance.
    """
    local = email.split('@')[0]
    if len(local) < min_length:
        return False
    return all(c in "0123456789abcdefABCDEF" for c in local)

def extract_emails_from_text(text: str) -> Set[str]:
    """Extract emails using regex and filter out invalid TLDs and hex-like local parts."""
    if not text:
        return set()
        
    found = set(EMAIL_REGEX.findall(text))
    valid_emails = set()
    
    for email in found:
        try:
            tld = email.split('@')[-1].split('.')[-1].lower()
            # Skip if TLD is invalid or the local part is hex-like (likely a UUID)
            if tld in INVALID_TLDS or is_hex_like_local_part(email):
                continue
            valid_emails.add(email)
        except IndexError:
            continue
            
    return valid_emails

@lru_cache(maxsize=256)
def convert_subdomain_to_www(url: str) -> str:
    """
    Convert subdomain URLs to main domain with www prefix.
    Uses tldextract to correctly handle multi-part TLDs and creative domains.
    Cached for performance.
    """
    parsed = urlparse(url)
    ext = tldextract.extract(url)
    
    # If there is a subdomain and it's not already 'www', replace it with 'www'
    if ext.subdomain and ext.subdomain != "www":
        new_netloc = f"www.{ext.domain}.{ext.suffix}"
        return urlunparse((parsed.scheme, new_netloc, parsed.path, parsed.params, parsed.query, parsed.fragment))
    else:
        return url

def fetch_page(url: str, timeout: int = 15) -> Tuple[Optional[str], Optional[str]]:
    """
    Attempt to fetch the content of a URL with error handling and timeouts.
    Returns a tuple (content, error) where content is the page text if successful,
    and error is None. If an error occurs, content is None and error holds the message.
    """
    try:
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8'
        }
        response = requests.get(url, headers=headers, timeout=timeout)
        if response.status_code == 200:
            return response.text, None
        else:
            return None, f"Status code {response.status_code}"
    except requests.exceptions.Timeout:
        return None, "Request timed out"
    except requests.exceptions.ConnectionError:
        return None, "Connection error"
    except requests.exceptions.RequestException as e:
        return None, str(e)
    except Exception as e:
        return None, f"Unexpected error: {str(e)}"

@lru_cache(maxsize=1024)
def normalize_url(url: str) -> str:
    """
    Normalize the URL by removing the query and fragment and stripping digits from the path.
    This helps in deduplicating shallow links that differ only by numbers or UUIDs.
    Cached for performance.
    """
    parsed = urlparse(url)
    clean_path = re.sub(r'\d+', '', parsed.path)
    normalized = urlunparse((parsed.scheme, parsed.netloc, clean_path, '', '', ''))
    return normalized

def get_shallow_links(root_url: str, html_content: str, max_links: int = 20) -> Set[str]:
    """
    From the HTML content of the root page, return a set of shallow internal links.
    A shallow link is defined as one that has a path with at most one level (ignoring the root).
    Deduplication is performed using normalized URLs.
    Limited to max_links (default 20).
    """
    if not html_content:
        return set()
        
    shallow_links = {}
    parsed_root = urlparse(root_url)
    base_domain = parsed_root.netloc

    try:
        soup = BeautifulSoup(html_content, 'html.parser')
        for tag in soup.find_all('a', href=True):
            # Stop if we've reached the maximum number of links
            if len(shallow_links) >= max_links:
                break
                
            link = tag['href']
            full_url = urljoin(root_url, link)
            parsed_link = urlparse(full_url)
            
            # Only include http/https links on the same domain with shallow paths
            if (parsed_link.scheme in ['http', 'https'] and 
                parsed_link.netloc == base_domain):
                path_parts = [part for part in parsed_link.path.split('/') if part]
                if len(path_parts) <= 1:
                    norm = normalize_url(full_url)
                    if norm not in shallow_links:
                        shallow_links[norm] = full_url
    except Exception as e:
        print(f"Error parsing HTML for links: {e}")
        
    return set(shallow_links.values())

def process_url(url: str) -> Tuple[str, Set[str], Optional[str]]:
    """
    Worker function for processing a single URL.
    Returns a tuple (url, emails, error) where emails is a set of found emails
    and error is any error message encountered.
    """
    print(f"Processing: {url}")
    content, error = fetch_page(url)
    if error:
        return url, set(), error
    emails = extract_emails_from_text(content)
    return url, emails, None

def extract_emails_from_website(url: str, max_links: int = 20) -> List[str]:
    """
    Advanced email extraction using parallel processing and shallow link crawling.
    Returns a list of unique emails found on the website.
    """
    try:
        # Initialize multiprocessing
        mp.freeze_support()  # For Windows compatibility
        
        # Convert subdomain to www if applicable
        url = convert_subdomain_to_www(url)
        print(f"Using URL: {url}")
        
        parsed = urlparse(url)
        
        # Define the root URL (entry page) as scheme://domain/
        root_url = f"{parsed.scheme}://{parsed.netloc}/"
        
        # First, process the provided URL and root URL
        urls_to_process = {url}
        if url != root_url:
            urls_to_process.add(root_url)
        
        # Get shallow links from root URL
        root_content, root_error = fetch_page(root_url)
        if not root_error and root_content:
            shallow_links = get_shallow_links(root_url, root_content, max_links=max_links)
            print(f"Found {len(shallow_links)} shallow links (limited to {max_links} max)")
            urls_to_process.update(shallow_links)
        
        # Process all URLs in parallel
        emails_found = set()
        
        # Determine the number of processes to use
        num_processes = min(mp.cpu_count(), len(urls_to_process))
        
        # Create a process pool and map the worker function to all URLs
        with mp.Pool(processes=num_processes) as pool:
            results = pool.map(process_url, urls_to_process)
        
        # Collect results
        for url, emails, error in results:
            if not error:
                emails_found.update(emails)
        
        if emails_found:
            print(f"Found {len(emails_found)} emails: {emails_found}")
        else:
            print("No emails found.")
            
        return list(emails_found)
    except Exception as e:
        print(f"Error extracting emails from {url}: {str(e)}")
        return []

# ------------------------------
# Place Details Functions
# ------------------------------
def get_text_search_places_page(api_key: str, query: str, latitude: float, longitude: float, 
                               radius: int = 1000, pagetoken: Optional[str] = None) -> Tuple[List[Dict], Optional[str]]:
    """
    Get a page of places using Text Search from Google Places API.
    Returns a tuple of (results, next_page_token).
    """
    url = "https://maps.googleapis.com/maps/api/place/textsearch/json"
    params = {
        "key": api_key,
        "query": query,
        "location": f"{latitude},{longitude}",
        "radius": radius
    }
    if pagetoken:
        params["pagetoken"] = pagetoken
        time.sleep(2)  # Required delay for next page token to become valid
        
    try:
        response = requests.get(url, params=params, timeout=15)
        data = response.json()
        
        if data.get("status") != "OK":
            print("Text search error or no more results:", data.get("status"))
            return [], None
            
        return data.get("results", []), data.get("next_page_token")
    except Exception as e:
        print(f"Error in text search: {e}")
        return [], None

def get_place_details(api_key: str, place_id: str, detail_fields: str) -> Dict:
    """
    Get detailed information about a place from Google Places API.
    Returns a dictionary of place details.
    """
    url = "https://maps.googleapis.com/maps/api/place/details/json"
    params = {
        "key": api_key,
        "place_id": place_id,
        "fields": detail_fields
    }
    
    try:
        response = requests.get(url, params=params, timeout=15)
        data = response.json()
        
        if data.get("status") != "OK":
            print(f"Error fetching details for place_id {place_id}: {data.get('status')}")
            return {}
            
        return data.get("result", {})
    except Exception as e:
        print(f"Error fetching place details: {e}")
        return {}

def flatten_value(value: Any) -> str:
    """Convert complex data types to JSON strings for CSV storage."""
    if isinstance(value, (dict, list)):
        return json.dumps(value, ensure_ascii=False)
    return str(value) if value is not None else ""

# ------------------------------
# H3 Hexagonal Grid Functions
# ------------------------------
def get_h3_resolution_for_size(km_size: float) -> int:
    """
    Get the appropriate H3 resolution for a desired hexagon size in kilometers.
    """
    # Resolution mapping based on approximate edge lengths
    if km_size > 100:
        return 2  # ~158 km
    elif km_size > 50:
        return 3  # ~60 km
    elif km_size > 20:
        return 4  # ~23 km
    elif km_size > 8:
        return 5  # ~8.5 km
    elif km_size > 3:
        return 6  # ~3.2 km
    elif km_size > 1:
        return 7  # ~1.2 km
    else:
        return 8  # ~0.46 km

def create_hexagonal_grid(center_lat: float, center_lng: float, 
                         radius_km: float, hex_size_km: float) -> List[Tuple[float, float, str]]:
    """
    Create a hexagonal grid around a center point.
    Returns a list of hexagon centers as (lat, lng, h3_index) tuples.
    """
    # Get appropriate H3 resolution for the desired hexagon size
    resolution = get_h3_resolution_for_size(hex_size_km)
    
    # Get the H3 index for the center point
    center_h3 = h3.geo_to_h3(center_lat, center_lng, resolution)
    
    # Calculate approximate hexagon edge length in km at this resolution
    hex_edge_km_map = {
        5: 8.5,
        6: 3.2,
        7: 1.2,
        8: 0.46
    }
    hex_edge_km = hex_edge_km_map.get(resolution, 40075.0 / (2**resolution * 6))
    
    # Calculate how many rings we need to cover the radius
    k_rings = max(1, int(radius_km / hex_edge_km))
    
    # Get all hexagons within k_rings of the center
    hexagons = h3.k_ring(center_h3, k_rings)
    
    # Convert H3 indexes to lat/lng centers
    hex_centers = []
    for h in hexagons:
        lat, lng = h3.h3_to_geo(h)
        hex_centers.append((lat, lng, h))
    
    return hex_centers

# ------------------------------
# File I/O Functions
# ------------------------------
def get_existing_place_ids(csv_path: str) -> Set[str]:
    """
    Read existing place IDs from a CSV file.
    Returns a set of place IDs.
    """
    if not os.path.exists(csv_path):
        return set()
        
    place_ids = set()
    try:
        with open(csv_path, 'r', encoding='utf-8', newline='') as f:
            reader = csv.DictReader(f)
            for row in reader:
                place_id = row.get('place_id', '')
                if place_id and place_id.strip():
                    # Remove quotes if present
                    place_id = place_id.strip('"\'')
                    place_ids.add(place_id)
    except Exception as e:
        print(f"Error reading existing place IDs from {csv_path}: {e}")
    
    return place_ids

def count_rows_in_csv(csv_path: str) -> int:
    """
    Count the number of rows in a CSV file, excluding the header.
    Returns the count as an integer.
    """
    if not os.path.exists(csv_path):
        return 0
        
    try:
        with open(csv_path, 'r', encoding='utf-8', newline='') as f:
            reader = csv.reader(f)
            # Skip header
            next(reader, None)
            # Count rows
            count = sum(1 for _ in reader)
        return count
    except Exception as e:
        print(f"Error counting rows in {csv_path}: {e}")
        return 0

def read_cities_from_csv(cities_csv_path: str) -> List[Tuple[str, float, float]]:
    """
    Read cities with their coordinates from a CSV file.
    Expected columns: city, lat, lng
    Returns a list of (city_name, lat, lng) tuples.
    """
    cities = []
    try:
        with open(cities_csv_path, 'r', encoding='utf-8', newline='') as f:
            reader = csv.DictReader(f)
            for row in reader:
                city_name = row.get('city', '')
                try:
                    lat = float(row.get('lat', 0))
                    lng = float(row.get('lng', 0))
                    if city_name and lat and lng:
                        cities.append((city_name, lat, lng))
                except (ValueError, TypeError):
                    print(f"Invalid coordinates for city {city_name}, skipping")
    except Exception as e:
        print(f"Error reading cities from {cities_csv_path}: {e}")
        
    return cities

def check_target_reached(csv_with_emails: str, target: int) -> bool:
    """
    Check if we've reached the target number of businesses with emails.
    Returns True if target is reached or exceeded, False otherwise.
    """
    current_count = count_rows_in_csv(csv_with_emails)
    if current_count >= target:
        print(f"Target of {target} businesses with emails reached! Current count: {current_count}")
        return True
    return False

# ------------------------------
# Processing Functions
# ------------------------------
def process_hexagon(api_key: str, lat: float, lng: float, h3_index: str, city_name: str, 
                   search_query: str, api_radius: int, existing_place_ids: Set[str], 
                   writer_with, writer_without, skip_domains: List[str], max_links: int, 
                   csv_with_emails: str, target_results: int, session_id: str) -> Tuple[int, Set[str]]:
    """
    Process a single hexagon completely, collecting all available place IDs using text search.
    Returns the number of businesses with emails found and the updated existing_place_ids set.
    """
    print(f"\nProcessing hexagon: {h3_index} at ({lat}, {lng}) in {city_name}")
    
    # Update current city in process state
    if session_id in processes:
        processes[session_id]['current_city'] = city_name
    
    businesses_with_email = 0
    pagetoken = None
    all_place_ids_in_hex = []
    
    # Step 1: Collect ALL place IDs from this hexagon using text search (exhaust all page tokens)
    while True:
        # Update progress for API calls
        if session_id in processes:
            processes[session_id]['api_calls'] += 1
            update_progress(session_id, target_results)
            
        page_results, pagetoken = get_text_search_places_page(
            api_key, search_query, lat, lng, api_radius, pagetoken
        )
        
        if not page_results:
            print("No more results for this hexagon.")
            break
        
        # Extract place IDs from this page
        all_place_ids_in_hex.extend(page_results)
        
        print(f"Collected {len(all_place_ids_in_hex)} place IDs so far from this hexagon.")
        
        # If no more pages, break
        if not pagetoken:
            break
            
        # Sleep to avoid hitting rate limits
        time.sleep(2)
        
        # Check if process was stopped
        if session_id in processes and not processes[session_id]['running']:
            print("Process was stopped by user.")
            return businesses_with_email, existing_place_ids
    
    # Step 2: Filter out place IDs that already exist in our database
    unique_places = []
    for place in all_place_ids_in_hex:
        place_id = place.get("place_id")
        if place_id and place_id not in existing_place_ids:
            unique_places.append(place)
            existing_place_ids.add(place_id)
    
    print(f"Found {len(unique_places)} unique place IDs out of {len(all_place_ids_in_hex)} total.")
    
    # Step 3: Process each unique place ID
    for i, place in enumerate(unique_places):
        # Check if process was stopped
        if session_id in processes and not processes[session_id]['running']:
            print("Process was stopped by user.")
            return businesses_with_email, existing_place_ids
            
        place_id = place.get("place_id")
        
        # Update progress for each place being processed
        if session_id in processes:
            processes[session_id]['places_processed'] += 1
            processes[session_id]['status'] = f"Processing place {i+1}/{len(unique_places)} in {city_name}"
            update_progress(session_id, target_results)
        
        # Get detailed information
        details = get_place_details(api_key, place_id, DETAIL_FIELDS)
        if not details:
            continue
            
        # Add H3 and city information
        details["h3_index"] = h3_index
        details["search_lat"] = lat
        details["search_lng"] = lng
        details["city"] = city_name
        
        # Attempt email extraction if website exists and is not in skip list
        website = details.get("website")
        emails = []
        
        if website:
            lower_site = website.lower()
            if any(skip in lower_site for skip in skip_domains):
                print(f"Skipping email extraction for {details.get('name', 'Unknown')} because website is {website}")
            else:
                print(f"Extracting emails for {details.get('name', 'Unknown')} from {website}")
                
                # Update status for email extraction
                if session_id in processes:
                    processes[session_id]['status'] = f"Extracting emails from {details.get('name', 'Unknown')} in {city_name}"
                    update_progress(session_id, target_results)
                    
                emails = extract_emails_from_website(website, max_links=max_links)
        
        details["emails"] = emails
            
        # Flatten the row for CSV writing
        row = {col: flatten_value(details.get(col, "")) for col in COLUMNS}
        
        # Write the row to the appropriate CSV file
        if emails:
            writer_with.writerow(row)
            businesses_with_email += 1
            print(f"Found business with email: {details.get('name', 'Unknown')}")
            
            # Update progress
            if session_id in processes:
                processes[session_id]['businesses_with_email'] += 1
                processes[session_id]['status'] = f"Found business with email: {details.get('name', 'Unknown')} in {city_name}"
                update_progress(session_id, target_results)
            
            # Check if we've reached the target after adding this business
            if check_target_reached(csv_with_emails, target_results):
                print("Target reached! Exiting program.")
                return businesses_with_email, existing_place_ids
        else:
            writer_without.writerow(row)
            if session_id in processes:
                processes[session_id]['businesses_without_email'] += 1
                update_progress(session_id, target_results)
    
    # Update progress after completing the hexagon
    if session_id in processes:
        processes[session_id]['hexagons_processed'] += 1
        update_progress(session_id, target_results)
    
    return businesses_with_email, existing_place_ids

def process_city(api_key: str, city_name: str, lat: float, lng: float, hex_size_km: float, 
                city_radius_km: float, search_query: str, api_radius: int, 
                existing_place_ids: Set[str], writer_with, writer_without, 
                skip_domains: List[str], max_links: int, 
                csv_with_emails: str, target_results: int, session_id: str) -> Tuple[int, Set[str]]:
    """
    Process an entire city by creating a hexagonal grid around it and processing each hexagon.
    Returns the number of businesses with emails found and the updated existing_place_ids set.
    """
    print(f"\n===== Processing City: {city_name} at ({lat}, {lng}) =====")
    
    # Update current city in process state
    if session_id in processes:
        processes[session_id]['current_city'] = city_name
        update_progress(session_id, target_results)
    
    # Create hexagonal grid for this city
    hex_centers = create_hexagonal_grid(lat, lng, city_radius_km, hex_size_km)
    print(f"Created {len(hex_centers)} hexagonal cells for {city_name}")
    
    # Update total hexagons count for progress tracking
    if session_id in processes:
        processes[session_id]['total_hexagons'] += len(hex_centers)
        update_progress(session_id, target_results)
    
    total_businesses_with_email = 0
    
    # Process each hexagon in this city
    for hex_index, (hex_lat, hex_lng, h3_index) in enumerate(hex_centers):
        # Check if process was stopped
        if session_id in processes and not processes[session_id]['running']:
            print("Process was stopped by user.")
            return total_businesses_with_email, existing_place_ids
            
        print(f"\nProcessing hexagon {hex_index+1}/{len(hex_centers)} in {city_name}")
        
        # Update status
        if session_id in processes:
            processes[session_id]['status'] = f"Processing city {city_name}, hexagon {hex_index+1}/{len(hex_centers)}"
            update_progress(session_id, target_results)
        
        # Process this hexagon completely
        businesses_with_email, existing_place_ids = process_hexagon(
            api_key, hex_lat, hex_lng, h3_index, city_name, search_query, api_radius,
            existing_place_ids, writer_with, writer_without, skip_domains, max_links,
            csv_with_emails, target_results, session_id
        )
        
        total_businesses_with_email += businesses_with_email
        
        # Check if target reached
        if check_target_reached(csv_with_emails, target_results):
            break
    
    # Update progress after completing the city
    if session_id in processes:
        processes[session_id]['cities_processed'] += 1
        update_progress(session_id, target_results)
    
    print(f"\nCompleted processing {city_name}. Found {total_businesses_with_email} businesses with emails.")
    return total_businesses_with_email, existing_place_ids

def update_progress(session_id: str, target_results: int):
    """Update the progress percentage based solely on businesses with emails collected"""
    if session_id not in processes:
        return
    
    process = processes[session_id]
    
    # Calculate progress as a simple percentage of businesses with emails found vs target
    if target_results > 0:
        progress_percentage = (process['businesses_with_email'] / target_results) * 100
    else:
        progress_percentage = 0
    
    # Cap at 100%
    progress_percentage = min(100, progress_percentage)
    
    # Update the progress
    process['progress'] = progress_percentage
    
    # Report progress
    progress_data = {
        "progress": process['progress'],
        "status": process['status'],
        "businesses_with_email": process['businesses_with_email'],
        "businesses_without_email": process['businesses_without_email'],
        "current_city": process.get('current_city', '')
    }
    print(f"PROGRESS: {json.dumps(progress_data)}")

# ------------------------------
# Main Processing Function
# ------------------------------
def run_scraper(session_id: str, api_key: str, cities_csv_path: str, target_results: int, search_query: str):
    """Run the scraper and update progress"""
    try:
        # Configuration
        HEX_SIZE_KM = 8  # Size of each hexagonal cell
        CITY_RADIUS_KM = 20  # Radius around each city to cover
        API_RADIUS = 5000  # Radius for each API call in meters (5km)
        MAX_LINKS = 20  # Maximum links to crawl per website for email extraction
        
        # CSV file paths
        CSV_WITH_EMAILS = os.path.join(app.config['OUTPUT_FOLDER'], f"{session_id}_business_with_emails.csv")
        CSV_WITHOUT_EMAILS = os.path.join(app.config['OUTPUT_FOLDER'], f"{session_id}_business_without_emails.csv")
        
        # Update output files in process state
        processes[session_id]['output_files'] = {
            'with_emails': f"{session_id}_business_with_emails.csv",
            'without_emails': f"{session_id}_business_without_emails.csv"
        }
        
        # List of domains to skip for email extraction
        skip_domains = ["facebook", "twitter", "instagram", "whatsapp", "x.com"]
        
        # Check if we've already reached the target before starting
        if check_target_reached(CSV_WITH_EMAILS, target_results):
            print(f"Target of {target_results} businesses with emails already reached. Exiting.")
            processes[session_id]['running'] = False
            processes[session_id]['status'] = "Target already reached"
            processes[session_id]['progress'] = 100
            return
        
        # Read cities from CSV
        cities = read_cities_from_csv(cities_csv_path)
        if not cities:
            print("No cities found in the CSV file. Please check the file format.")
            processes[session_id]['running'] = False
            processes[session_id]['status'] = "No cities found in CSV"
            return
        
        print(f"Loaded {len(cities)} cities from {cities_csv_path}")
        
        # Get existing place IDs from CSV files
        existing_place_ids = set()
        existing_place_ids.update(get_existing_place_ids(CSV_WITH_EMAILS))
        existing_place_ids.update(get_existing_place_ids(CSV_WITHOUT_EMAILS))
        print(f"Found {len(existing_place_ids)} existing place IDs in CSV files")
        
        # Initialize progress tracking counters
        processes[session_id]['total_cities'] = len(cities)
        processes[session_id]['cities_processed'] = 0
        processes[session_id]['total_hexagons'] = 0
        processes[session_id]['hexagons_processed'] = 0
        processes[session_id]['places_processed'] = 0
        processes[session_id]['api_calls'] = 0
        processes[session_id]['current_city'] = ""
        
        # Initialize CSV files
        file_mode = 'a' if os.path.exists(CSV_WITH_EMAILS) else 'w'
        write_header = file_mode == 'w'
        
        csv_with = open(CSV_WITH_EMAILS, mode=file_mode, newline='', encoding="utf-8")
        csv_without = open(CSV_WITHOUT_EMAILS, mode=file_mode, newline='', encoding="utf-8")
        
        try:
            writer_with = csv.DictWriter(csv_with, fieldnames=COLUMNS)
            writer_without = csv.DictWriter(csv_without, fieldnames=COLUMNS)
            
            if write_header:
                writer_with.writeheader()
                writer_without.writeheader()
            
            current_businesses_with_email = count_rows_in_csv(CSV_WITH_EMAILS)
            print(f"Starting with {current_businesses_with_email} businesses with emails")
            
            # Process cities one by one
            for city_index, (city_name, lat, lng) in enumerate(cities):
                # Check if process was stopped
                if not processes[session_id]['running']:
                    print("Process was stopped by user.")
                    break
                    
                # Check if target is reached before processing a new city
                if check_target_reached(CSV_WITH_EMAILS, target_results):
                    print(f"Target of {target_results} businesses with emails reached. Stopping.")
                    break
                
                # Process this city
                businesses_with_email, existing_place_ids = process_city(
                    api_key, city_name, lat, lng, HEX_SIZE_KM, CITY_RADIUS_KM, search_query, API_RADIUS,
                    existing_place_ids, writer_with, writer_without, skip_domains, MAX_LINKS,
                    CSV_WITH_EMAILS, target_results, session_id
                )
                
                # Flush the CSV files to ensure data is written
                csv_with.flush()
                csv_without.flush()
                    
            print(f"\nProcessing complete. Found {count_rows_in_csv(CSV_WITH_EMAILS)} businesses with emails.")
            print(f"Results saved to {CSV_WITH_EMAILS} and {CSV_WITHOUT_EMAILS}")
        
        finally:
            # Always close the CSV files
            csv_with.close()
            csv_without.close()
        
        # Final progress update
        if session_id in processes:
            processes[session_id]['running'] = False
            processes[session_id]['status'] = "Process completed"
            processes[session_id]['progress'] = 100
            update_progress(session_id, target_results)
            
    except Exception as e:
        print(f"Error in scraper: {str(e)}")
        if session_id in processes:
            processes[session_id]['running'] = False
            processes[session_id]['status'] = f"Error: {str(e)}"

# ------------------------------
# Flask Routes
# ------------------------------
@app.route('/')
def index():
    # Generate a unique session ID if not exists
    if 'session_id' not in session:
        session['session_id'] = str(uuid.uuid4())
    
    return render_template('index.html')

@app.route('/upload', methods=['POST'])
def upload_file():
    if 'cities_csv' not in request.files:
        return jsonify({'error': 'No file part'}), 400
    
    file = request.files['cities_csv']
    if file.filename == '':
        return jsonify({'error': 'No selected file'}), 400
    
    if not file.filename.endswith('.csv'):
        return jsonify({'error': 'File must be a CSV'}), 400
    
    # Save the file
    session_id = session.get('session_id', str(uuid.uuid4()))
    filename = secure_filename(f"{session_id}_{file.filename}")
    filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
    file.save(filepath)
    
    return jsonify({'success': True, 'filename': filename})

@app.route('/start', methods=['POST'])
def start_process():
    session_id = session.get('session_id')
    if not session_id:
        return jsonify({'error': 'Invalid session'}), 400
    
    # Check if process is already running
    if session_id in processes and processes[session_id].get('running', False):
        return jsonify({'error': 'A process is already running'}), 400
    
    # Get parameters
    data = request.json
    api_key = data.get('api_key')
    filename = data.get('filename')
    target_results = int(data.get('target_results', 100))
    search_query = data.get('search_query', 'restaurant')
    
    if not api_key or not filename:
        return jsonify({'error': 'API key and filename are required'}), 400
    
    # Setup process tracking
    processes[session_id] = {
        'running': True,
        'progress': 0,
        'status': 'Starting...',
        'businesses_with_email': 0,
        'businesses_without_email': 0,
        'total_cities': 0,
        'cities_processed': 0,
        'total_hexagons': 0,
        'hexagons_processed': 0,
        'places_processed': 0,
        'api_calls': 0,
        'current_city': '',
        'output_files': {
            'with_emails': f"{session_id}_business_with_emails.csv",
            'without_emails': f"{session_id}_business_without_emails.csv"
        }
    }
    
    # Start the process in a thread
    thread = threading.Thread(
        target=run_scraper,
        args=(
            session_id,
            api_key,
            os.path.join(app.config['UPLOAD_FOLDER'], filename),
            target_results,
            search_query
        )
    )
    thread.daemon = True
    thread.start()
    
    return jsonify({'success': True})

@app.route('/progress')
def get_progress():
    session_id = session.get('session_id')
    if not session_id or session_id not in processes:
        return jsonify({
            'running': False,
            'progress': 0,
            'status': 'No process running',
            'businesses_with_email': 0,
            'businesses_without_email': 0,
            'current_city': '',
            'stats': {
                'total_cities': 0,
                'cities_processed': 0,
                'total_hexagons': 0,
                'hexagons_processed': 0,
                'places_processed': 0,
                'api_calls': 0
            }
        })
    
    return jsonify({
        'running': processes[session_id].get('running', False),
        'progress': processes[session_id].get('progress', 0),
        'status': processes[session_id].get('status', ''),
        'businesses_with_email': processes[session_id].get('businesses_with_email', 0),
        'businesses_without_email': processes[session_id].get('businesses_without_email', 0),
        'current_city': processes[session_id].get('current_city', ''),
        'stats': {
            'total_cities': processes[session_id].get('total_cities', 0),
            'cities_processed': processes[session_id].get('cities_processed', 0),
            'total_hexagons': processes[session_id].get('total_hexagons', 0),
            'hexagons_processed': processes[session_id].get('hexagons_processed', 0),
            'places_processed': processes[session_id].get('places_processed', 0),
            'api_calls': processes[session_id].get('api_calls', 0)
        }
    })

@app.route('/reset')
def reset_process():
    session_id = session.get('session_id')
    if not session_id:
        return jsonify({'error': 'Invalid session'}), 400
    
    # Stop any running process
    if session_id in processes and processes[session_id].get('running', False):
        processes[session_id]['running'] = False
    
    # Create a new session ID
    new_session_id = str(uuid.uuid4())
    session['session_id'] = new_session_id
    
    # Clear process data
    if session_id in processes:
        del processes[session_id]
    
    return jsonify({'success': True, 'new_session_id': new_session_id})

@app.route('/stop')
def stop_process():
    session_id = session.get('session_id')
    if not session_id or session_id not in processes:
        return jsonify({'error': 'No process running'}), 400
    
    # Stop the process but keep the data
    processes[session_id]['running'] = False
    processes[session_id]['status'] = 'Stopped by user. Data is available for download.'
    
    return jsonify({'success': True})

@app.route('/download/<file_type>')
def download_file(file_type):
    session_id = session.get('session_id')
    if not session_id or session_id not in processes:
        return jsonify({'error': 'No process data available'}), 400
    
    if file_type not in ['with_emails', 'without_emails']:
        return jsonify({'error': 'Invalid file type'}), 400
    
    filename = processes[session_id]['output_files'][file_type]
    filepath = os.path.join(app.config['OUTPUT_FOLDER'], filename)
    
    if not os.path.exists(filepath):
        # If file doesn't exist, create an empty one with headers
        try:
            with open(filepath, 'w', newline='', encoding='utf-8') as f:
                writer = csv.DictWriter(f, fieldnames=COLUMNS)
                writer.writeheader()
        except Exception as e:
            return jsonify({'error': f'Failed to create file: {str(e)}'}), 500
    
    return send_file(
        filepath,
        as_attachment=True,
        download_name=f"business_{file_type}.csv",
        mimetype='text/csv'
    )

if __name__ == '__main__':
    app.run(debug=True)

