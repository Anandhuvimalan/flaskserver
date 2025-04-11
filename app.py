# Optimize imports by removing unused ones and grouping related imports
import os
import csv
import json
import time
import threading
import uuid
import re
import h3
import multiprocessing as mp
from functools import lru_cache
from urllib.parse import urlparse, urljoin, urlunparse
from bs4 import BeautifulSoup
from typing import Set, List, Dict, Tuple, Optional, Any, Union
from werkzeug.utils import secure_filename
import tldextract
import requests
from flask import Flask, render_template, request, jsonify, send_file, session
import geopandas as gpd
import shapely.geometry
from shapely.geometry import shape, Point, Polygon, MultiPolygon
from geojson import Feature, FeatureCollection, Point as GeoPoint
from concurrent.futures import ThreadPoolExecutor
from shapely.prepared import prep

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
# Optimize email extraction with a more efficient regex pattern
EMAIL_REGEX = re.compile(r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b', re.IGNORECASE | re.DOTALL)
INVALID_TLDS = {
    'png', 'jpg', 'jpeg', 'gif', 'svg', 'webp', 'bmp', 'ico', 'tiff',
    'css', 'js', 'pdf', 'doc', 'docx', 'xls', 'xlsx', 'ppt', 'pptx', 'zip'
}

# Social media regex patterns
FACEBOOK_REGEX = re.compile(
    r'https:\/\/(?:www\.)?facebook\.com[^"\s\\]*', re.IGNORECASE
)

TWITTER_X_REGEX = re.compile(
    r'https:\/\/(?:www\.)?(?:twitter\.com|x\.com)[^"\s\\]*', re.IGNORECASE
)

INSTAGRAM_REGEX = re.compile(
    r'https:\/\/(?:www\.)?instagram\.com[^"\s\\]*', re.IGNORECASE
)

LINKEDIN_REGEX = re.compile(
    r'https:\/\/(?:www\.)?linkedin\.com\/(?:company|in|school|organization)[^"\s\\]*', re.IGNORECASE
)

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
    # Social media links
    "facebook", "twitter_x", "instagram", "linkedin",
    # Location info
    "h3_index", "search_lat", "search_lng", "city"
]

# H3 resolution options
H3_RESOLUTIONS = {
    6: {"name": "Large (Res 6)", "avg_edge_length_km": 3.2, "search_radius": 3000},
    7: {"name": "Medium (Res 7)", "avg_edge_length_km": 1.2, "search_radius": 1200},
    8: {"name": "Small (Res 8)", "avg_edge_length_km": 0.46, "search_radius": 500}
}

# Default H3 resolution
DEFAULT_H3_RESOLUTION = 7

# ------------------------------
# Email and Social Media Extraction Functions
# ------------------------------
# Increase cache size for better performance
@lru_cache(maxsize=2048)
def is_hex_like_local_part(email: str, min_length: int = 16) -> bool:
    """
    Check if the local part of an email (before the @) is composed solely of hex digits
    and is at least min_length long. Uses LRU cache for performance.
    """
    local = email.split('@')[0]
    if len(local) < min_length:
        return False
    return all(c in "0123456789abcdefABCDEF" for c in local)

# Optimize the extract_emails_from_text function
def extract_emails_from_text(text: str) -> Set[str]:
    """Extract emails using regex and filter out invalid TLDs and hex-like local parts."""
    if not text:
        return set()
        
    # Use a set comprehension for better performance
    found = set(EMAIL_REGEX.findall(text))
    
    # Use a set comprehension instead of iterating and adding
    return {
        email for email in found 
        if not (email.split('@')[-1].split('.')[-1].lower() in INVALID_TLDS or is_hex_like_local_part(email))
    }

def extract_social_links_from_text(text: str) -> Dict[str, List[str]]:
    """Extract social media links from text. Returns lists of links for each platform."""
    if not text:
        return {"facebook": [], "twitter_x": [], "instagram": [], "linkedin": []}
    
    social_links = {
        "facebook": [],
        "twitter_x": [],
        "instagram": [],
        "linkedin": []
    }
    
    # Find Facebook links
    facebook_matches = FACEBOOK_REGEX.findall(text)
    if facebook_matches:
        social_links["facebook"] = list(set(facebook_matches))  # Remove duplicates
    
    # Find Twitter/X links
    twitter_x_matches = TWITTER_X_REGEX.findall(text)
    if twitter_x_matches:
        social_links["twitter_x"] = list(set(twitter_x_matches))  # Remove duplicates
    
    # Find Instagram links
    instagram_matches = INSTAGRAM_REGEX.findall(text)
    if instagram_matches:
        social_links["instagram"] = list(set(instagram_matches))  # Remove duplicates
    
    # Find LinkedIn links
    linkedin_matches = LINKEDIN_REGEX.findall(text)
    if linkedin_matches:
        social_links["linkedin"] = list(set(linkedin_matches))  # Remove duplicates
    
    return social_links

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

# Optimize the process_url function to handle errors more efficiently
def process_url(url: str) -> Tuple[str, Set[str], Dict[str, List[str]], Optional[str]]:
    """
    Worker function for processing a single URL.
    Returns a tuple (url, emails, social_links, error) where emails is a set of found emails,
    social_links is a dictionary of lists of social media links, and error is any error message encountered.
    """
    try:
        content, error = fetch_page(url)
        if error:
            return url, set(), {"facebook": [], "twitter_x": [], "instagram": [], "linkedin": []}, error
        
        # Process content in parallel
        emails = extract_emails_from_text(content)
        social_links = extract_social_links_from_text(content)
        
        return url, emails, social_links, None
    except Exception as e:
        return url, set(), {"facebook": [], "twitter_x": [], "instagram": [], "linkedin": []}, str(e)

# Optimize the extract_emails_and_social_from_website function to use ThreadPoolExecutor
def extract_emails_and_social_from_website(url: str, max_links: int = 20) -> Tuple[List[str], Dict[str, List[str]]]:
    """
    Advanced email and social media extraction using parallel processing and shallow link crawling.
    Returns a tuple of (list of unique emails found, dictionary of lists of social media links).
    """
    try:
        # Convert subdomain to www if applicable
        url = convert_subdomain_to_www(url)
        
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
            urls_to_process.update(shallow_links)
        
        # Process all URLs in parallel using ThreadPoolExecutor instead of multiprocessing
        # This is more efficient for I/O-bound tasks like web scraping
        emails_found = set()
        social_links = {
            "facebook": [],
            "twitter_x": [],
            "instagram": [],
            "linkedin": []
        }
        
        # Use ThreadPoolExecutor for better performance with I/O-bound tasks
        with ThreadPoolExecutor(max_workers=min(32, len(urls_to_process))) as executor:
            results = list(executor.map(process_url, urls_to_process))
        
        # Collect results more efficiently
        for url, emails, page_social_links, error in results:
            if not error:
                emails_found.update(emails)
                
                # Update social links if found - ensure no duplicates
                for platform in social_links:
                    # Create a set of existing links for efficient lookup
                    existing_links = set(social_links[platform])
                    # Add only new links that don't already exist
                    social_links[platform].extend([
                        link for link in page_social_links[platform] 
                        if link not in existing_links
                    ])
                    # Update the existing_links set
                    existing_links.update(page_social_links[platform])
        
        return list(emails_found), social_links
    except Exception as e:
        return [], {"facebook": [], "twitter_x": [], "instagram": [], "linkedin": []}

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

# Optimize the generate_hexagons function for better performance
def generate_hexagons(boundary_geometry, h3_resolution):
    """
    Generate H3 hexagons that cover a boundary geometry.
    Optimized for better performance with complex geometries.
    """
    # Get the bounding box of the boundary
    minx, miny, maxx, maxy = boundary_geometry.bounds
    
    # Convert to lat/lng coordinates
    min_lat, max_lat = miny, maxy
    min_lng, max_lng = minx, maxx
    
    # Create a grid of points within the bounding box
    # Use adaptive grid density based on boundary size
    area = boundary_geometry.area
    grid_density = min(50, max(20, int(30 * (area / 10))))  # Adaptive grid density
    
    lat_step = (max_lat - min_lat) / grid_density
    lng_step = (max_lng - min_lng) / grid_density
    
    # Generate H3 indexes for the grid points more efficiently
    h3_indexes = set()
    
    # Create a list of points first
    grid_points = []
    for i in range(grid_density + 1):
        lat = min_lat + i * lat_step
        for j in range(grid_density + 1):
            lng = min_lng + j * lng_step
            grid_points.append((lat, lng))
    
    # Use a more efficient approach for point-in-polygon tests
    # Create a prepared geometry for faster contains checks
    prepared_geometry = prep(boundary_geometry)
    
    # Process points in batches
    for lat, lng in grid_points:
        point = Point(lng, lat)
        if prepared_geometry.contains(point) or prepared_geometry.touches(point):
            h3_index = h3.geo_to_h3(lat, lng, h3_resolution)
            h3_indexes.add(h3_index)
    
    # For each H3 index, get the hexagon boundary
    # If any part of the hexagon intersects with the boundary, keep it
    intersecting_indexes = set()
    
    # Process in batches for better performance
    batch_size = 100
    h3_index_list = list(h3_indexes)
    
    for i in range(0, len(h3_index_list), batch_size):
        batch = h3_index_list[i:i+batch_size]
        for h3_index in batch:
            hex_boundary = h3.h3_to_geo_boundary(h3_index)
            # Convert to a Shapely polygon
            hex_polygon = Polygon([(lng, lat) for lat, lng in hex_boundary])
            if boundary_geometry.intersects(hex_polygon):
                intersecting_indexes.add(h3_index)
    
    # For complex boundaries, we might miss some areas
    # Use k-ring to fill in gaps - use a more efficient approach
    all_indexes = set(intersecting_indexes)
    
    # Process in batches
    intersecting_list = list(intersecting_indexes)
    for i in range(0, len(intersecting_list), batch_size):
        batch = intersecting_list[i:i+batch_size]
        for h3_index in batch:
            # Add neighbors (k=1 is usually sufficient)
            neighbors = h3.k_ring(h3_index, 1)
            for neighbor in neighbors:
                if neighbor not in all_indexes:
                    # Check if this neighbor intersects with the boundary
                    hex_boundary = h3.h3_to_geo_boundary(neighbor)
                    hex_polygon = Polygon([(lng, lat) for lat, lng in hex_boundary])
                    if boundary_geometry.intersects(hex_polygon):
                        all_indexes.add(neighbor)
    
    # Convert H3 indexes to (lat, lng, h3_index) tuples
    hexagons = []
    for h3_index in all_indexes:
        lat, lng = h3.h3_to_geo(h3_index)
        hexagons.append((lat, lng, h3_index))
    
    return hexagons

def get_search_radius_for_resolution(resolution):
    """
    Get the appropriate search radius in meters for a given H3 resolution.
    """
    if resolution in H3_RESOLUTIONS:
        return H3_RESOLUTIONS[resolution]["search_radius"]
    else:
        # Default to 1000m if resolution not found
        return 1000

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
# GeoJSON and Hexagon Functions
# ------------------------------
def load_geojson(file_path):
    """
    Load a GeoJSON file and return a GeoDataFrame.
    """
    try:
        gdf = gpd.read_file(file_path)
        return gdf
    except Exception as e:
        print(f"Error loading GeoJSON file: {e}")
        return None

# Update the detect_boundary_type function to look for specific properties
def detect_boundary_type(gdf):
    """
    Detect if the GeoJSON contains districts or regions based on column names and values.
    Returns 'district', 'region', or 'unknown'.
    """
    # Convert all column names to lowercase for case-insensitive matching
    columns = [col.lower() for col in gdf.columns]
    
    # Check for TYPE_2 or ENGTYPE_2 columns that indicate district
    if 'type_2' in columns or 'engtype_2' in columns:
        # If these columns exist, check their values
        if 'type_2' in columns and any(str(val).lower() == 'district' for val in gdf['TYPE_2'] if val):
            return 'district'
        if 'engtype_2' in columns and any(str(val).lower() == 'district' for val in gdf['ENGTYPE_2'] if val):
            return 'district'
    
    # Check for NAME_2 column which typically contains district names
    if 'name_2' in columns:
        return 'district'
    
    # Check for NAME_1 column which typically contains region names
    if 'name_1' in columns and 'name_2' not in columns:
        return 'region'
    
    # Check for district-related columns
    if any('district' in col for col in columns):
        return 'district'
    
    # Check for region-related columns
    if any('region' in col for col in columns):
        return 'region'
    
    # If we can't determine, return unknown
    return 'unknown'

# Update the extract_boundaries function to handle the specific GeoJSON structure
def extract_boundaries(gdf, boundary_type):
    """
    Extract boundaries from the GeoDataFrame based on the specific GeoJSON structure.
    Returns a list of dictionaries with name, country, and geometry.
    """
    
    boundaries = []
    
    # Check if we have the expected columns for New Zealand districts
    has_nz_structure = all(col in gdf.columns for col in ['COUNTRY', 'NAME_1', 'NAME_2'])
    
    if has_nz_structure:
        print("Detected New Zealand GeoJSON structure")
        
        # Process each row in the GeoDataFrame
        for idx, row in gdf.iterrows():
            if row.geometry:
                # Get country
                country = row.get('COUNTRY', '')
                
                # Get region (NAME_1)
                region = row.get('NAME_1', '')
                
                # Get district (NAME_2)
                district = row.get('NAME_2', '')
                
                # Get district type
                district_type = row.get('TYPE_2', '') or row.get('ENGTYPE_2', '')
                
                # Create a name that includes region and district
                if district and region:
                    name = f"{district}, {region}"
                elif district:
                    name = district
                elif region:
                    name = region
                else:
                    name = f"Boundary {idx+1}"
                
                boundaries.append({
                    'name': name,
                    'country': country,
                    'region': region,
                    'district': district,
                    'type': district_type,
                    'geometry': row.geometry,
                    'index': idx  # Add index for reference
                })
    else:
        # Fall back to generic extraction if we don't have the expected structure
        print("Using generic GeoJSON extraction")
        
        # Try to find the name column based on boundary type
        name_columns = []
        if boundary_type == 'district':
            name_columns = ['district', 'district_name', 'name_2', 'name', 'dist_name']
        elif boundary_type == 'region':
            name_columns = ['region', 'region_name', 'name_1', 'name', 'reg_name']
        else:
            name_columns = ['name', 'area_name', 'boundary_name']
        
        # Find the first matching column that exists
        name_col = None
        for col in name_columns:
            matching_cols = [c for c in gdf.columns if col.lower() in c.lower()]
            if matching_cols:
                name_col = matching_cols[0]
                break
        
        # If no name column found, use index as name
        if not name_col:
            print(f"No name column found for {boundary_type} boundaries. Using index as name.")
            for idx, row in gdf.iterrows():
                if row.geometry:
                    boundaries.append({
                        'name': f"{boundary_type.capitalize()} {idx+1}",
                        'country': '',
                        'region': '',
                        'district': '',
                        'type': boundary_type,
                        'geometry': row.geometry,
                        'index': idx  # Add index for reference
                    })
        else:
            for idx, row in gdf.iterrows():
                if row.geometry:
                    boundaries.append({
                        'name': str(row[name_col]),
                        'country': row.get('COUNTRY', ''),
                        'region': row.get('NAME_1', ''),
                        'district': row.get('NAME_2', ''),
                        'type': boundary_type,
                        'geometry': row.geometry,
                        'index': idx  # Add index for reference
                    })
    
    return boundaries

# Update the create_geojson_feature_collection function to include more properties
def create_geojson_feature_collection(boundaries, hexagons_by_boundary):
    """
    Create a GeoJSON FeatureCollection with boundaries and their hexagons.
    """
    features = []
    
    # Add boundary features
    for i, boundary in enumerate(boundaries):
        # Create a feature for the boundary
        properties = {
            "name": boundary["name"],
            "type": "boundary",
            "index": i,
            "country": boundary.get("country", ""),
            "region": boundary.get("region", ""),
            "district": boundary.get("district", ""),
            "boundary_type": boundary.get("type", "")
        }
        
        geometry = shapely.geometry.mapping(boundary["geometry"])
        feature = Feature(geometry=geometry, properties=properties)
        features.append(feature)
        
        # Add hexagon features for this boundary if available
        if i in hexagons_by_boundary:
            for hex_tuple in hexagons_by_boundary[i]:
                lat, lng, h3_index = hex_tuple
                hex_properties = {
                    "name": f"Hexagon {h3_index}",
                    "type": "hexagon",
                    "h3_index": h3_index,
                    "boundary_index": i,
                    "boundary_name": boundary["name"]
                }
                
                # Create a point feature for the hexagon center
                point_geom = {"type": "Point", "coordinates": [lng, lat]}
                hex_feature = Feature(geometry=point_geom, properties=hex_properties)
                features.append(hex_feature)
    
    return FeatureCollection(features)

# Add this function to create a GeoJSON feature for the current processing state
def create_current_state_geojson(boundary, hexagons, current_hexagon=None, processed_hexagons=None):
    """
    Create a GeoJSON FeatureCollection for the current processing state.
    
    Args:
        boundary: The boundary being processed
        hexagons: List of hexagons for this boundary
        current_hexagon: The current hexagon being processed (optional)
        processed_hexagons: Set of hexagons that have been processed (optional)
        
    Returns:
        A GeoJSON FeatureCollection with the boundary and hexagons
    """
    features = []
    
    # Initialize processed_hexagons if not provided
    if processed_hexagons is None:
        processed_hexagons = set()
    
    # Add the boundary feature
    if boundary:
        properties = {
            "name": boundary["name"],
            "type": "boundary",
            "country": boundary.get("country", ""),
            "region": boundary.get("region", ""),
            "district": boundary.get("district", ""),
            "boundary_type": boundary.get("type", ""),
            "is_current": True
        }
        
        # Convert Shapely geometry to GeoJSON format
        geometry = shapely.geometry.mapping(boundary["geometry"])
        feature = Feature(geometry=geometry, properties=properties)
        features.append(feature)
    
    # Add hexagon features
    if hexagons:
        for hex_tuple in hexagons:
            lat, lng, h3_index = hex_tuple
            
            # Determine hexagon status
            status = "pending"  # Default status (blue)
            if h3_index in processed_hexagons:
                status = "processed"  # Completed (yellow)
            elif current_hexagon and h3_index == current_hexagon:
                status = "current"  # Currently processing (red)
            
            # Get hexagon boundary for polygon representation
            hex_boundary = h3.h3_to_geo_boundary(h3_index)
            # Make sure to close the polygon by repeating the first point
            hex_coords = [[lng, lat] for lat, lng in hex_boundary]
            if hex_coords and hex_coords[0] != hex_coords[-1]:
                hex_coords.append(hex_coords[0])
            
            hex_properties = {
                "name": f"Hexagon {h3_index}",
                "type": "hexagon",
                "h3_index": h3_index,
                "boundary_name": boundary["name"] if boundary else "",
                "is_current": current_hexagon and h3_index == current_hexagon,
                "status": status
            }
            
            # Create a polygon feature for the hexagon
            hex_geom = {
                "type": "Polygon",
                "coordinates": [hex_coords]
            }
            hex_feature = Feature(geometry=hex_geom, properties=hex_properties)
            features.append(hex_feature)
    
    # Create and return the FeatureCollection
    return FeatureCollection(features)

# ------------------------------
# Processing Functions
# ------------------------------
# Optimize the process_hexagon function
def process_hexagon(api_key: str, lat: float, lng: float, h3_index: str, boundary_name: str, 
                   search_query: str, api_radius: int, existing_place_ids: Set[str], 
                   writer_with, writer_without, skip_domains: List[str], max_links: int, 
                   csv_with_emails: str, target_results: int, session_id: str) -> Tuple[int, Set[str]]:
    """
    Process a single hexagon completely, collecting all available place IDs using text search.
    Returns the number of businesses with emails found and the updated existing_place_ids set.
    """
    # Update current boundary and hexagon in process state
    if session_id in processes:
        processes[session_id]['current_boundary'] = boundary_name
        processes[session_id]['current_hexagon'] = h3_index
        
        # Update current state GeoJSON if we have the boundary
        if 'current_boundary_obj' in processes[session_id]:
            boundary = processes[session_id]['current_boundary_obj']
            hexagons = processes[session_id].get('current_boundary_hexagons', [])
            processed_hexagons = processes[session_id].get('processed_hexagons', set())
            
            # Create GeoJSON for current state
            current_state_geojson = create_current_state_geojson(
                boundary, 
                hexagons, 
                h3_index,
                processed_hexagons
            )
            
            # Save to file
            current_state_path = os.path.join(app.config['OUTPUT_FOLDER'], f"{session_id}_current_state.geojson")
            with open(current_state_path, 'w') as f:
                json.dump(current_state_geojson, f)
            
            processes[session_id]['current_state_geojson'] = f"{session_id}_current_state.geojson"
    
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
            break
        
        # Extract place IDs from this page
        all_place_ids_in_hex.extend(page_results)
        
        # If no more pages, break
        if not pagetoken:
            break
            
        # Sleep to avoid hitting rate limits
        time.sleep(2)
        
        # Check if process was stopped
        if session_id in processes and not processes[session_id]['running']:
            return businesses_with_email, existing_place_ids
    
    # Step 2: Filter out place IDs that already exist in our database more efficiently
    # Use a dictionary comprehension for better performance
    unique_places = [
        place for place in all_place_ids_in_hex 
        if place.get("place_id") and place.get("place_id") not in existing_place_ids
    ]
    
    # Update existing_place_ids with new place IDs
    existing_place_ids.update(place.get("place_id") for place in unique_places if place.get("place_id"))
    
    # Step 3: Process each unique place ID
    # Only create ThreadPoolExecutor if there are places to process
    if not unique_places:
        # No unique places to process, return early
        return businesses_with_email, existing_place_ids
        
    # Use ThreadPoolExecutor for better performance with I/O-bound tasks
    with ThreadPoolExecutor(max_workers=min(10, max(1, len(unique_places)))) as executor:
        # Create a list of tasks
        futures = []
        for i, place in enumerate(unique_places):
            # Check if process was stopped
            if session_id in processes and not processes[session_id]['running']:
                return businesses_with_email, existing_place_ids
                
            place_id = place.get("place_id")
            
            # Update progress for each place being processed
            if session_id in processes:
                processes[session_id]['places_processed'] += 1
                processes[session_id]['status'] = f"Processing place {i+1}/{len(unique_places)} in {boundary_name}"
                update_progress(session_id, target_results)
            
            # Submit the task to the executor
            futures.append(executor.submit(
                process_place, 
                api_key, place_id, h3_index, lat, lng, boundary_name, 
                skip_domains, max_links
            ))
        
        # Process results as they complete
        for future in futures:
            try:
                details, emails = future.result()
                if not details:
                    continue
                    
                # Flatten the row for CSV writing
                row = {col: flatten_value(details.get(col, "")) for col in COLUMNS}
                
                # Write the row to the appropriate CSV file
                if emails:
                    writer_with.writerow(row)
                    businesses_with_email += 1
                    
                    # Update progress
                    if session_id in processes:
                        processes[session_id]['businesses_with_email'] += 1
                        processes[session_id]['status'] = f"Found business with email: {details.get('name', 'Unknown')} in {boundary_name}"
                        update_progress(session_id, target_results)
                    
                    # Check if we've reached the target after adding this business
                    if check_target_reached(csv_with_emails, target_results):
                        return businesses_with_email, existing_place_ids
                else:
                    writer_without.writerow(row)
                    if session_id in processes:
                        processes[session_id]['businesses_without_email'] += 1
                        update_progress(session_id, target_results)
            except Exception as e:
                # Log the error but continue processing
                print(f"Error processing place: {e}")
    
    # At the end of the function, mark this hexagon as processed
    if session_id in processes:
        if 'processed_hexagons' not in processes[session_id]:
            processes[session_id]['processed_hexagons'] = set()
        processes[session_id]['processed_hexagons'].add(h3_index)
    
    return businesses_with_email, existing_place_ids

# Add a new helper function to process a single place
def process_place(api_key, place_id, h3_index, lat, lng, boundary_name, skip_domains, max_links):
    """Process a single place and return its details and emails."""
    # Get detailed information
    details = get_place_details(api_key, place_id, DETAIL_FIELDS)
    if not details:
        return None, []
        
    # Add H3 and boundary information
    details["h3_index"] = h3_index
    details["search_lat"] = lat
    details["search_lng"] = lng
    details["city"] = boundary_name  # Use boundary name instead of city
    
    # Attempt email and social media extraction if website exists and is not in skip list
    website = details.get("website")
    emails = []
    social_links = {"facebook": [], "twitter_x": [], "instagram": [], "linkedin": []}
    
    if website:
        lower_site = website.lower()
        if not any(skip in lower_site for skip in skip_domains):
            emails, social_links = extract_emails_and_social_from_website(website, max_links=max_links)
    
    details["emails"] = emails
    details["facebook"] = social_links["facebook"]
    details["twitter_x"] = social_links["twitter_x"]
    details["instagram"] = social_links["instagram"]
    details["linkedin"] = social_links["linkedin"]
    
    return details, emails

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
    """Update the progress percentage based on businesses with emails collected"""
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
        "current_boundary": process.get('current_boundary', ''),
        "current_hexagon": process.get('current_hexagon', '')
    }
    print(f"PROGRESS: {json.dumps(progress_data)}")

# ------------------------------
# Main Processing Function
# ------------------------------
# Optimize the run_scraper function
def run_scraper(session_id, api_key, geojson_file_path, target_results, search_query, h3_resolution, selected_boundaries=None):
    """
    Run the scraper with GeoJSON input and update progress.
    Optimized for better performance and memory usage.
    """
    try:
        # Configuration
        API_RADIUS = get_search_radius_for_resolution(h3_resolution)
        MAX_LINKS = 20  # Maximum links to crawl per website for email extraction
        
        # CSV file paths
        CSV_WITH_EMAILS = os.path.join(app.config['OUTPUT_FOLDER'], f"{session_id}_business_with_emails.csv")
        CSV_WITHOUT_EMAILS = os.path.join(app.config['OUTPUT_FOLDER'], f"{session_id}_business_without_emails.csv")
        
        # Update output files in process state
        processes[session_id]['output_files'] = {
            'with_emails': f"{session_id}_business_with_emails.csv",
            'without_emails': f"{session_id}_business_without_emails.csv"
        }
        
        # Initialize processed hexagons set
        processes[session_id]['processed_hexagons'] = set()
        
        # List of domains to skip for email extraction
        skip_domains = ["facebook", "twitter", "instagram", "whatsapp", "x.com"]
        
        # Check if we've already reached the target before starting
        if check_target_reached(CSV_WITH_EMAILS, target_results):
            processes[session_id]['running'] = False
            processes[session_id]['status'] = "Target already reached"
            processes[session_id]['progress'] = 100
            return
        
        # Load GeoJSON file
        gdf = load_geojson(geojson_file_path)
        if gdf is None or gdf.empty:
            processes[session_id]['running'] = False
            processes[session_id]['status'] = "Failed to load GeoJSON file"
            return
        
        # Detect boundary type
        boundary_type = detect_boundary_type(gdf)
        
        # Extract boundaries
        all_boundaries = extract_boundaries(gdf, boundary_type)
        if not all_boundaries:
            processes[session_id]['running'] = False
            processes[session_id]['status'] = "No valid boundaries found"
            return
        
        # Filter boundaries if selected_boundaries is provided
        if selected_boundaries is not None and len(selected_boundaries) > 0:
            # Convert selected_boundaries to a set of indices for faster lookup
            selected_indices = set(selected_boundaries)
            boundaries = [b for b in all_boundaries if b['index'] in selected_indices]
        else:
            boundaries = all_boundaries
        
        # Update process state with boundary information - store only serializable data
        processes[session_id]['boundary_info'] = {
            'type': boundary_type,
            'count': len(boundaries),
            'names': [b['name'] for b in boundaries],
            'total_count': len(all_boundaries),
            'selected_count': len(boundaries)
        }
        
        # Get existing place IDs from CSV files
        existing_place_ids = set()
        existing_place_ids.update(get_existing_place_ids(CSV_WITH_EMAILS))
        existing_place_ids.update(get_existing_place_ids(CSV_WITHOUT_EMAILS))
        
        # Initialize progress tracking counters
        processes[session_id]['total_boundaries'] = len(boundaries)
        processes[session_id]['boundaries_processed'] = 0
        processes[session_id]['total_hexagons'] = 0  # Will be updated for each boundary
        processes[session_id]['hexagons_processed'] = 0
        processes[session_id]['places_processed'] = 0
        processes[session_id]['api_calls'] = 0
        processes[session_id]['current_boundary'] = ""
        processes[session_id]['current_hexagon'] = ""
        
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
            
            # Process boundaries one by one
            for boundary_index, boundary in enumerate(boundaries):
                # Check if process was stopped
                if not processes[session_id]['running']:
                    break
                    
                # Check if target is reached before processing a new boundary
                if check_target_reached(CSV_WITH_EMAILS, target_results):
                    break
                
                boundary_name = boundary['name']
                
                # Update current boundary in process state
                processes[session_id]['current_boundary'] = boundary_name
                processes[session_id]['boundaries_processed'] = boundary_index
                processes[session_id]['current_boundary_obj'] = boundary
                update_progress(session_id, target_results)
                
                # Generate hexagons for this boundary only
                hexagons = generate_hexagons(boundary['geometry'], h3_resolution)
                
                # Store hexagons for current boundary in process state
                processes[session_id]['current_boundary_hexagons'] = hexagons
                processes[session_id]['total_hexagons'] = len(hexagons)
                processes[session_id]['hexagons_processed'] = 0
                
                # Create current state GeoJSON for this boundary
                current_state_geojson = create_current_state_geojson(boundary, hexagons, None, processes[session_id]['processed_hexagons'])
                current_state_path = os.path.join(app.config['OUTPUT_FOLDER'], f"{session_id}_current_state.geojson")
                with open(current_state_path, 'w') as f:
                    json.dump(current_state_geojson, f)
                
                processes[session_id]['current_state_geojson'] = f"{session_id}_current_state.geojson"
                
                # Process each hexagon in this boundary
                total_businesses_with_email = 0
                
                for hex_index, (hex_lat, hex_lng, h3_index) in enumerate(hexagons):
                    # Check if process was stopped
                    if not processes[session_id]['running']:
                        break
                        
                    # Update status
                    if session_id in processes:
                        processes[session_id]['status'] = f"Processing {boundary_type} {boundary_name}, hexagon {hex_index+1}/{len(hexagons)}"
                        processes[session_id]['hexagons_processed'] = hex_index + 1
                        processes[session_id]['current_hexagon'] = h3_index
                        update_progress(session_id, target_results)
                        
                        # Update current state GeoJSON with current hexagon
                        current_state_geojson = create_current_state_geojson(boundary, hexagons, h3_index, processes[session_id]['processed_hexagons'])
                        with open(current_state_path, 'w') as f:
                            json.dump(current_state_geojson, f)
                    
                    # Process this hexagon completely
                    businesses_with_email, existing_place_ids = process_hexagon(
                        api_key, hex_lat, hex_lng, h3_index, boundary_name, search_query, API_RADIUS,
                        existing_place_ids, writer_with, writer_without, skip_domains, MAX_LINKS,
                        CSV_WITH_EMAILS, target_results, session_id
                    )
                    
                    total_businesses_with_email += businesses_with_email
                    
                    # Check if target reached
                    if check_target_reached(CSV_WITH_EMAILS, target_results):
                        break
                
                # Update progress after completing the boundary
                if session_id in processes:
                    processes[session_id]['boundaries_processed'] += 1
                    update_progress(session_id, target_results)
                
                # Flush the CSV files to ensure data is written
                csv_with.flush()
                csv_without.flush()
        
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
        import traceback
        traceback.print_exc()
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
    if 'geojson_file' not in request.files:
        return jsonify({'error': 'No file part'}), 400
    
    file = request.files['geojson_file']
    if file.filename == '':
        return jsonify({'error': 'No selected file'}), 400
    
    if not file.filename.endswith(('.geojson', '.json')):
        return jsonify({'error': 'File must be a GeoJSON (.geojson or .json)'}), 400
    
    # Save the file
    session_id = session.get('session_id', str(uuid.uuid4()))
    filename = secure_filename(f"{session_id}_{file.filename}")
    filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
    file.save(filepath)
    
    # Try to load the file to validate it's a proper GeoJSON
    try:
        gdf = gpd.read_file(filepath)
        if gdf is None or gdf.empty:
            return jsonify({'error': 'Invalid or empty GeoJSON file'}), 400
        
        # Detect boundary type
        boundary_type = detect_boundary_type(gdf)
        
        # Extract boundaries
        boundaries = extract_boundaries(gdf, boundary_type)
        if not boundaries:
            return jsonify({'error': 'No valid boundaries found in the GeoJSON file'}), 400
        
        # Return boundary information with indices for selection
        boundary_info = []
        for boundary in boundaries:
            boundary_info.append({
                'index': boundary['index'],
                'name': boundary['name'],
                'country': boundary.get('country', ''),
                'region': boundary.get('region', ''),
                'district': boundary.get('district', '')
            })
        
        return jsonify({
            'success': True, 
            'filename': filename,
            'boundary_type': boundary_type,
            'boundaries_count': len(boundaries),
            'boundaries': boundary_info
        })
    except Exception as e:
        return jsonify({'error': f'Error processing GeoJSON file: {str(e)}'}), 400

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
    h3_resolution = int(data.get('h3_resolution', DEFAULT_H3_RESOLUTION))
    selected_boundaries = data.get('selected_boundaries', None)  # New parameter for boundary selection
    
    if not api_key or not filename:
        return jsonify({'error': 'API key and filename are required'}), 400
    
    # Validate H3 resolution
    if h3_resolution not in H3_RESOLUTIONS:
        return jsonify({'error': f'Invalid H3 resolution. Valid options are: {", ".join(map(str, H3_RESOLUTIONS.keys()))}'}), 400
    
    # Setup process tracking
    processes[session_id] = {
        'running': True,
        'progress': 0,
        'status': 'Starting...',
        'businesses_with_email': 0,
        'businesses_without_email': 0,
        'total_boundaries': 0,
        'boundaries_processed': 0,
        'total_hexagons': 0,
        'hexagons_processed': 0,
        'places_processed': 0,
        'api_calls': 0,
        'current_boundary': '',
        'current_hexagon': '',
        'output_files': {
            'with_emails': f"{session_id}_business_with_emails.csv",
            'without_emails': f"{session_id}_business_without_emails.csv"
        },
        'h3_resolution': h3_resolution,
        'h3_resolution_info': H3_RESOLUTIONS[h3_resolution],
        'processed_hexagons': set(),  # Track processed hexagons
        'selected_boundaries': selected_boundaries  # Store selected boundaries
    }
    
    # Start the process in a thread
    thread = threading.Thread(
        target=run_scraper,
        args=(
            session_id,
            api_key,
            os.path.join(app.config['UPLOAD_FOLDER'], filename),
            target_results,
            search_query,
            h3_resolution,
            selected_boundaries  # Pass selected boundaries to run_scraper
        )
    )
    thread.daemon = True
    thread.start()
    
    return jsonify({'success': True})

# Modify the get_progress route to handle non-serializable objects
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
            'current_boundary': '',
            'current_hexagon': '',
            'stats': {
                'total_boundaries': 0,
                'boundaries_processed': 0,
                'total_hexagons': 0,
                'hexagons_processed': 0,
                'places_processed': 0,
                'api_calls': 0
            }
        })
    
    # Get boundary info if available but exclude non-serializable objects
    boundary_info = processes[session_id].get('boundary_info', {})
    
    # Remove non-serializable objects from boundary_info
    if 'boundaries' in boundary_info:
        del boundary_info['boundaries']
    
    # Check if we have current state GeoJSON
    current_state_geojson = processes[session_id].get('current_state_geojson', None)
    
    return jsonify({
        'running': processes[session_id].get('running', False),
        'progress': processes[session_id].get('progress', 0),
        'status': processes[session_id].get('status', ''),
        'businesses_with_email': processes[session_id].get('businesses_with_email', 0),
        'businesses_without_email': processes[session_id].get('businesses_without_email', 0),
        'current_boundary': processes[session_id].get('current_boundary', ''),
        'current_hexagon': processes[session_id].get('current_hexagon', ''),
        'stats': {
            'total_boundaries': processes[session_id].get('total_boundaries', 0),
            'boundaries_processed': processes[session_id].get('boundaries_processed', 0),
            'total_hexagons': processes[session_id].get('total_hexagons', 0),
            'hexagons_processed': processes[session_id].get('hexagons_processed', 0),
            'places_processed': processes[session_id].get('places_processed', 0),
            'api_calls': processes[session_id].get('api_calls', 0)
        },
        'boundary_info': boundary_info,
        'h3_resolution': processes[session_id].get('h3_resolution', DEFAULT_H3_RESOLUTION),
        'h3_resolution_info': processes[session_id].get('h3_resolution_info', {}),
        'current_state_geojson': current_state_geojson,
        'selected_boundaries': processes[session_id].get('selected_boundaries', None)
    })

@app.route('/geojson')
def get_geojson():
    session_id = session.get('session_id')
    if not session_id or session_id not in processes:
        return jsonify({'error': 'No process data available'}), 400
    
    boundary_info = processes[session_id].get('boundary_info', {})
    if not boundary_info or 'geojson_path' not in boundary_info:
        return jsonify({'error': 'No GeoJSON data available'}), 404
    
    geojson_path = os.path.join(app.config['OUTPUT_FOLDER'], boundary_info['geojson_path'])
    if not os.path.exists(geojson_path):
        return jsonify({'error': 'GeoJSON file not found'}), 404
    
    return send_file(
        geojson_path,
        as_attachment=False,
        mimetype='application/json'
    )

@app.route('/current_state')
def get_current_state():
    session_id = session.get('session_id')
    if not session_id or session_id not in processes:
        return jsonify({'error': 'No process data available'}), 400
    
    current_state_geojson = processes[session_id].get('current_state_geojson')
    if not current_state_geojson:
        return jsonify({'error': 'No current state data available'}), 404
    
    geojson_path = os.path.join(app.config['OUTPUT_FOLDER'], current_state_geojson)
    if not os.path.exists(geojson_path):
        return jsonify({'error': 'Current state GeoJSON file not found'}), 404
    
    return send_file(
        geojson_path,
        as_attachment=False,
        mimetype='application/json'
    )

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
