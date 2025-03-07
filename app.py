import os
import csv
import re
import requests
import googlemaps
from time import sleep
from urllib.parse import urlparse, urljoin
from bs4 import BeautifulSoup
from flask import Flask, render_template, request, redirect, url_for, send_file, flash, jsonify
import threading
import logging
import math
import random
from geopy.geocoders import Nominatim
from shapely.geometry import Point, Polygon
import numpy as np
from sklearn.cluster import KMeans

# Set up logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

app = Flask(__name__)
app.secret_key = "your_secret_key"  # Needed for flash messages

# Global API key (initially empty, so you must set it via the admin panel)
API_KEY = ""

# Global progress tracker
progress_info = {
    "current": 0,
    "total": 0,
    "last_business": "",
    "complete": False,
    "error": "",
    "skipped": 0,
    "pages_crawled": 0,
    "debug_info": "",
    "stopped": False  # Flag to track if extraction was manually stopped
}

# Global list to track skipped businesses
skipped_businesses = []

# Helper function to create a business data dictionary with all fields
def create_business_data_dict(details, include_email=False, email='', reason=''):
    """Create a complete business data dictionary from place details"""
    business_data = {
        'Place ID': details.get('place_id', ''),
        'Name': details.get('name', ''),
        'Delivery': details.get('delivery', ''),
        'Opening Hours': str(details.get('opening_hours', '')),
        'Serves Brunch': details.get('serves_brunch', ''),
        'Rating': details.get('rating', ''),
        'Editorial Summary': details.get('editorial_summary', ''),
        'Serves Breakfast': details.get('serves_breakfast', ''),
        'International Phone Number': details.get('international_phone_number', ''),
        'User Ratings Total': details.get('user_ratings_total', ''),
        'Curbside Pickup': details.get('curbside_pickup', ''),
        'Plus Code': str(details.get('plus_code', '')),
        'Formatted Phone Number': details.get('formatted_phone_number', ''),
        'Vicinity': details.get('vicinity', ''),
        'Coordinates': get_coordinates_string(details),
        'Serves Vegetarian Food': details.get('serves_vegetarian_food', ''),
        'Takeout': details.get('takeout', ''),
        'Price Level': details.get('price_level', ''),
        'Dine In': details.get('dine_in', ''),
        'Serves Lunch': details.get('serves_lunch', ''),
        'Icon': details.get('icon', ''),
        'Reservable': details.get('reservable', ''),
        'URL': details.get('url', ''),
        'Type': ', '.join(details.get('type', [])) if isinstance(details.get('type', []), list) else details.get('type', ''),
        'Reviews': str(details.get('reviews', '')),
        'Serves Wine': details.get('serves_wine', ''),
        'ADR Address': details.get('adr_address', ''),
        'Permanently Closed': details.get('permanently_closed', ''),
        'UTC Offset': details.get('utc_offset', ''),
        'Current Opening Hours': str(details.get('current_opening_hours', '')),
        'Secondary Opening Hours': str(details.get('secondary_opening_hours', '')),
        'Website': details.get('website', ''),
        'Photo': str(details.get('photo', '')),
        'Business Status': details.get('business_status', ''),
        'Serves Beer': details.get('serves_beer', ''),
        'Review': str(details.get('review', '')),
        'Formatted Address': details.get('formatted_address', ''),
        'Serves Dinner': details.get('serves_dinner', ''),
        'Wheelchair Accessible Entrance': details.get('wheelchair_accessible_entrance', ''),
        'Country': get_country_from_formatted_address(details.get('formatted_address', ''))
    }
    
    if include_email:
        business_data['Email'] = email
    else:
        business_data['Email'] = ''
        business_data['Reason'] = reason
        
    return business_data

# -------------------- Google Maps Client Helper --------------------

def get_gmaps_client():
    """Return a new Google Maps client if API_KEY is set; otherwise raise an error."""
    global API_KEY
    if not API_KEY:
        raise ValueError("API key is not set. Please set it via the api setup page.")
    return googlemaps.Client(key=API_KEY)

# -------------------- Helper Functions --------------------

def get_business_details(place_id):
    """Get detailed information about a place using its place_id"""
    client = get_gmaps_client()
    fields = [
        'place_id',
        'delivery',
        'opening_hours',
        'serves_brunch',
        'rating',
        'editorial_summary',
        'name',
        'serves_breakfast',
        'international_phone_number',
        'user_ratings_total',
        'curbside_pickup',
        'plus_code',
        'formatted_phone_number',
        'vicinity',
        'geometry',  # includes location (lat, lng)
        'serves_vegetarian_food',
        'takeout',
        'price_level',
        'dine_in',
        'serves_lunch',
        'icon',
        'reservable',
        'url',
        'type',
        'reviews',
        'serves_wine',
        'adr_address',
        'permanently_closed',
        'utc_offset',
        'current_opening_hours',
        'secondary_opening_hours',
        'website',
        'photo',
        'business_status',
        'serves_beer',
        'review',
        'formatted_address',
        'serves_dinner',
        'wheelchair_accessible_entrance'
    ]
    try:
        place_details = client.place(place_id=place_id, fields=fields)
        return place_details.get('result', {})
    except Exception as e:
        logger.error(f"Error getting place details for {place_id}: {str(e)}")
        return {}

INVALID_TLDS = {
    'png', 'jpg', 'jpeg', 'gif', 'svg', 'webp', 'bmp', 'ico', 'tiff',
    'css', 'js', 'pdf', 'doc', 'docx', 'xls', 'xlsx', 'ppt', 'pptx', 'zip'
}

def crawl_website_for_emails(start_url, max_pages=None):
    """
    Crawl the website starting from start_url, following internal links up to max_pages,
    and extract email addresses from all pages.
    
    If max_pages is None, it will crawl until no more pages are found.
    """
    global progress_info
    visited = set()
    emails = set()
    to_visit = [start_url]
    parsed_base = urlparse(start_url)
    base_domain = parsed_base.netloc

    # Add common contact pages to visit first
    contact_paths = ['/contact', '/contact-us', '/about', '/about-us', '/support']
    for path in contact_paths:
        contact_url = f"{parsed_base.scheme}://{base_domain}{path}"
        if contact_url not in to_visit:
            to_visit.append(contact_url)

    pages_crawled = 0
    while to_visit and (max_pages is None or pages_crawled < max_pages):
        # Check if the extraction has been stopped
        if progress_info["stopped"]:
            progress_info["debug_info"] = "Extraction stopped manually. Saving collected data."
            break
            
        current_url = to_visit.pop(0)
        if current_url in visited:
            continue
            
        visited.add(current_url)
        pages_crawled += 1
        progress_info["pages_crawled"] = pages_crawled
        
        try:
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
                'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8',
                'Accept-Language': 'en-US,en;q=0.5',
                'Connection': 'keep-alive',
                'Upgrade-Insecure-Requests': '1',
                'Cache-Control': 'max-age=0',
            }
            response = requests.get(current_url, timeout=10, headers=headers)
            if response.status_code != 200:
                continue
            html_content = response.text

            # Extract emails from current page using multiple regex patterns
            # Standard email pattern
            found_emails = re.findall(
                r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b',
                html_content,
                re.IGNORECASE
            )
            
            # Look for "mailto:" links
            mailto_emails = re.findall(
                r'mailto:([A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,})',
                html_content,
                re.IGNORECASE
            )
            
            # Look for emails with text like "Email:" or "Contact:"
            context_emails = re.findall(
                r'(?:email|contact|mail|e-mail|email us at)[^\w\d]*([A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,})',
                html_content,
                re.IGNORECASE
            )
            
            # Combine all found emails
            all_emails = found_emails + mailto_emails + context_emails
            
            for email in all_emails:
                domain_part = email.split('@')[-1].lower()
                tld = domain_part.split('.')[-1]
                if tld not in INVALID_TLDS:
                    emails.add(email)

            # If we found emails, we can stop crawling this website
            if emails:
                progress_info["debug_info"] = f"Found {len(emails)} emails after crawling {pages_crawled} pages"
                return emails

            # Parse the page to find internal links
            soup = BeautifulSoup(html_content, 'html.parser')
            for link in soup.find_all('a', href=True):
                href = link.get('href')
                # Resolve relative URLs to absolute URLs
                next_url = urljoin(current_url, href)
                parsed_next = urlparse(next_url)
                # Only consider HTTP/HTTPS links within the same domain
                if parsed_next.scheme in ['http', 'https'] and parsed_next.netloc == base_domain:
                    if next_url not in visited and next_url not in to_visit:
                        to_visit.append(next_url)
        except Exception as e:
            logger.error(f"Error crawling {current_url}: {str(e)}")
            continue

    return emails

def extract_emails_from_website(url, max_pages=None):
    """
    Extract email addresses by deeply crawling the website for all its contents.
    If the provided URL is not the homepage, the homepage is used as the starting point.
    
    If max_pages is None, it will crawl until no more pages are found.
    """
    try:
        parsed_url = urlparse(url)
        homepage_url = f"{parsed_url.scheme}://{parsed_url.netloc}"
        emails = crawl_website_for_emails(homepage_url, max_pages=max_pages)
        return list(emails)
    except Exception as e:
        logger.error(f"Error extracting emails from {url}: {str(e)}")
        return []

def get_country_from_formatted_address(formatted_address):
    """Extract the country from a formatted address string.
    
    Assumes that the country is the last element after splitting by comma.
    """
    if not formatted_address:
        return ''
    parts = formatted_address.split(',')
    return parts[-1].strip() if parts else ''

def get_coordinates_string(details):
    """Extract coordinates from place details"""
    if 'geometry' in details and 'location' in details['geometry']:
        loc = details['geometry']['location']
        return f"{loc.get('lat', '')}, {loc.get('lng', '')}"
    return ''

def save_to_csv(data, filename):
    """Save the extracted data to a CSV file"""
    if not data:
        # Create an empty file if no data
        with open(filename, 'w', newline='', encoding='utf-8') as f:
            f.write('')
        return
        
    fieldnames = data[0].keys()
    with open(filename, 'w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(data)

def save_skipped_to_csv(data, filename):
    """Save the skipped businesses to a CSV file"""
    if not data:
        # Create an empty file if no data
        with open(filename, 'w', newline='', encoding='utf-8') as f:
            f.write('')
        return
        
    fieldnames = data[0].keys()
    with open(filename, 'w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(data)

def calculate_dynamic_max_pages(num_results):
    """Calculate a dynamic max_pages value based on the number of results requested"""
    if num_results <= 100:
        return 30  # For small result sets, crawl up to 30 pages per website
    elif num_results <= 500:
        return 50  # For medium result sets, crawl up to 50 pages per website
    elif num_results <= 1000:
        return 100  # For large result sets, crawl up to 100 pages per website
    else:
        # For very large result sets, no limit - will crawl until emails are found or no more pages
        return None

# -------------------- Advanced Geographical Search Functions --------------------

def get_location_info(lat, lng):
    """
    Get detailed information about a location using reverse geocoding.
    Returns the country, administrative areas, and locality information.
    """
    try:
        geolocator = Nominatim(user_agent="business_email_extractor")
        location = geolocator.reverse((lat, lng), exactly_one=True)
        
        if location and location.raw.get('address'):
            address = location.raw['address']
            return {
                'country': address.get('country'),
                'country_code': address.get('country_code'),
                'state': address.get('state') or address.get('region'),
                'county': address.get('county'),
                'city': address.get('city') or address.get('town') or address.get('village'),
                'suburb': address.get('suburb'),
                'postcode': address.get('postcode'),
                'display_name': location.raw.get('display_name', ''),
                'type': location.raw.get('type', '')
            }
    except Exception as e:
        logger.error(f"Error in reverse geocoding: {str(e)}")
    
    return {
        'country': None,
        'country_code': None,
        'state': None,
        'county': None,
        'city': None,
        'suburb': None,
        'postcode': None,
        'display_name': '',
        'type': ''
    }

def get_country_boundaries(country_code):
    """
    Get the approximate boundaries of a country.
    Returns a bounding box (min_lat, min_lng, max_lat, max_lng).
    
    This is a simplified version. In a production environment, you would use
    a more accurate source of country boundaries like a GeoJSON database.
    """
    # This is a simplified mapping of country codes to bounding boxes
    # In a real application, you would use a more comprehensive database
    country_bounds = {
        'us': (24.396308, -125.000000, 49.384358, -66.934570),  # USA
        'ca': (41.676556, -141.001944, 83.110626, -52.619055),  # Canada
        'gb': (49.674, -8.623555, 61.061, 2.0),                 # UK
        'au': (-43.658, 112.911057, -9.221, 159.109219),        # Australia
        'in': (6.747139, 68.162386, 37.097, 97.395555),         # India
        'de': (47.270111, 5.866944, 55.099167, 15.041944),      # Germany
        'fr': (41.371, -5.142222, 51.092, 9.561944),            # France
        # Add more countries as needed
    }
    
    # Default to a global bounding box if country not found
    return country_bounds.get(country_code.lower(), (-90, -180, 90, 180))

def get_administrative_boundaries(country_code, state=None):
    """
    Get the approximate boundaries of an administrative area (state/province).
    Returns a bounding box (min_lat, min_lng, max_lat, max_lng).
    
    This is a simplified version. In a production environment, you would use
    a more accurate source of administrative boundaries like a GeoJSON database.
    """
    # This would be a mapping of state/province codes to bounding boxes
    # In a real application, you would use a more comprehensive database
    # For now, we'll return the country boundaries
    return get_country_boundaries(country_code)

# Replace the generate_adaptive_search_points function with this improved version
def generate_adaptive_search_points(location, num_results):
    """
    Generate search points based on the location context.
    Uses a progressive expansion approach to ensure we find enough businesses.
    
    Args:
        location: Tuple of (latitude, longitude)
        num_results: Number of results requested
    
    Returns:
        List of (lat, lng) tuples for search points
    """
    lat, lng = location
    
    # Get information about the location
    location_info = get_location_info(lat, lng)
    progress_info["debug_info"] = f"Location identified as: {location_info['display_name']}"
    
    # Calculate the initial number of points based on the requested results
    initial_points_count = min(500, max(50, num_results * 2))
    
    # Calculate the initial search radius based on the number of results
    # More requested results = larger initial search radius
    initial_radius_km = min(50, max(10, num_results / 20))
    
    # Generate multiple layers of search points with increasing radii
    search_points = []
    
    # Layer 1: Immediate vicinity (small radius)
    search_points.extend(generate_radius_based_points(lat, lng, initial_radius_km, int(initial_points_count * 0.2)))
    
    # Layer 2: Medium vicinity
    search_points.extend(generate_radius_based_points(lat, lng, initial_radius_km * 2, int(initial_points_count * 0.3)))
    
    # Layer 3: Wider area
    search_points.extend(generate_radius_based_points(lat, lng, initial_radius_km * 5, int(initial_points_count * 0.3)))
    
    # Layer 4: Regional area
    search_points.extend(generate_radius_based_points(lat, lng, initial_radius_km * 10, int(initial_points_count * 0.2)))
    
    # For very large result sets, add even more expansive layers
    if num_results > 100:
        # Layer 5: Extended regional area
        search_points.extend(generate_radius_based_points(lat, lng, initial_radius_km * 20, int(initial_points_count * 0.2)))
    
    if num_results > 500:
        # Layer 6: State/province level
        search_points.extend(generate_radius_based_points(lat, lng, initial_radius_km * 50, int(initial_points_count * 0.2)))
    
    if num_results > 1000:
        # Layer 7: Country level
        if location_info['country_code']:
            bounds = get_country_boundaries(location_info['country_code'])
            search_points.extend(generate_strategic_points_in_bounds(bounds, int(initial_points_count * 0.3)))
    
    # Ensure we have enough search points
    if len(search_points) < initial_points_count:
        # Add more points with an even larger radius
        additional_points_needed = initial_points_count - len(search_points)
        search_points.extend(generate_radius_based_points(lat, lng, initial_radius_km * 100, additional_points_needed))
    
    # Shuffle the points to ensure we don't search in a strictly expanding pattern
    random.shuffle(search_points)
    
    progress_info["debug_info"] = f"Generated {len(search_points)} search points across multiple distance layers"
    
    return search_points

def generate_strategic_points_in_bounds(bounds, num_points):
    """
    Generate strategic search points within a bounding box.
    Uses a combination of grid, population-weighted, and random points.
    
    Args:
        bounds: Tuple of (min_lat, min_lng, max_lat, max_lng)
        num_points: Number of points to generate
    
    Returns:
        List of (lat, lng) tuples
    """
    min_lat, min_lng, max_lat, max_lng = bounds
    
    # Calculate the number of points for each strategy
    grid_points_count = int(num_points * 0.6)  # 60% grid points
    random_points_count = int(num_points * 0.3)  # 30% random points
    strategic_points_count = num_points - grid_points_count - random_points_count  # Remaining for strategic points
    
    # Generate grid points
    grid_points = generate_grid_points_in_bounds(bounds, grid_points_count)
    
    # Generate random points
    random_points = generate_random_points_in_bounds(bounds, random_points_count)
    
    # Generate strategic points (e.g., major cities, business centers)
    # In a real application, you would use a database of major cities/business centers
    # For now, we'll use a simplified approach with some strategic offsets
    strategic_points = []
    
    # Add the center point
    center_lat = (min_lat + max_lat) / 2
    center_lng = (min_lng + max_lng) / 2
    strategic_points.append((center_lat, center_lng))
    
    # Add points at 1/4 and 3/4 positions
    quarter_lat = min_lat + (max_lat - min_lat) / 4
    three_quarter_lat = min_lat + 3 * (max_lat - min_lat) / 4
    quarter_lng = min_lng + (max_lng - min_lng) / 4
    three_quarter_lng = min_lng + 3 * (max_lng - min_lng) / 4
    
    strategic_points.extend([
        (quarter_lat, quarter_lng),
        (quarter_lat, three_quarter_lng),
        (three_quarter_lat, quarter_lng),
        (three_quarter_lat, three_quarter_lng)
    ])
    
    # Fill remaining strategic points with random points
    remaining_points = strategic_points_count - len(strategic_points)
    if remaining_points > 0:
        strategic_points.extend(generate_random_points_in_bounds(bounds, remaining_points))
    
    # Combine all points
    all_points = grid_points + random_points + strategic_points
    
    # Ensure we have the requested number of points
    if len(all_points) > num_points:
        all_points = all_points[:num_points]
    
    return all_points

def generate_grid_points_in_bounds(bounds, num_points):
    """
    Generate a grid of points within a bounding box.
    
    Args:
        bounds: Tuple of (min_lat, min_lng, max_lat, max_lng)
        num_points: Number of points to generate
    
    Returns:
        List of (lat, lng) tuples
    """
    min_lat, min_lng, max_lat, max_lng = bounds
    
    # Calculate grid dimensions
    grid_size = int(math.sqrt(num_points))
    
    # Generate grid points
    points = []
    for i in range(grid_size):
        for j in range(grid_size):
            # Calculate normalized position in grid (0 to 1)
            norm_i = i / (grid_size - 1) if grid_size > 1 else 0.5
            norm_j = j / (grid_size - 1) if grid_size > 1 else 0.5
            
            # Calculate actual lat/lng
            lat = min_lat + norm_i * (max_lat - min_lat)
            lng = min_lng + norm_j * (max_lng - min_lng)
            
            points.append((lat, lng))
    
    return points

def generate_random_points_in_bounds(bounds, num_points):
    """
    Generate random points within a bounding box.
    
    Args:
        bounds: Tuple of (min_lat, min_lng, max_lat, max_lng)
        num_points: Number of points to generate
    
    Returns:
        List of (lat, lng) tuples
    """
    min_lat, min_lng, max_lat, max_lng = bounds
    
    points = []
    for _ in range(num_points):
        lat = min_lat + random.random() * (max_lat - min_lat)
        lng = min_lng + random.random() * (max_lng - min_lng)
        points.append((lat, lng))
    
    return points

def generate_radius_based_points(center_lat, center_lng, radius_km, num_points):
    """
    Generate points within a radius around a center point.
    Uses a combination of concentric circles and random points.
    
    Args:
        center_lat: Center latitude
        center_lng: Center longitude
        radius_km: Radius in kilometers
        num_points: Number of points to generate
    
    Returns:
        List of (lat, lng) tuples
    """
    # Calculate the approximate degrees for the given radius
    # 1 degree of latitude is approximately 111 km
    lat_degree_radius = radius_km / 111.0
    # 1 degree of longitude varies with latitude, approximately cos(lat) * 111 km
    lng_degree_radius = radius_km / (111.0 * math.cos(math.radians(center_lat)))
    
    # Generate points in concentric circles
    points = []
    
    # Add the center point
    points.append((center_lat, center_lng))
    
    # Number of circles
    num_circles = min(10, int(num_points / 10))
    
    # Points per circle
    points_per_circle = int((num_points - 1) / num_circles)
    
    for circle_idx in range(num_circles):
        # Calculate the radius of this circle (0 to 1)
        circle_radius_factor = (circle_idx + 1) / num_circles
        
        # Calculate the actual radius in degrees
        circle_lat_radius = lat_degree_radius * circle_radius_factor
        circle_lng_radius = lng_degree_radius * circle_radius_factor
        
        # Calculate points on this circle
        for point_idx in range(points_per_circle):
            # Calculate the angle for this point (0 to 2π)
            angle = 2 * math.pi * point_idx / points_per_circle
            
            # Calculate the point coordinates
            lat = center_lat + circle_lat_radius * math.sin(angle)
            lng = center_lng + circle_lng_radius * math.cos(angle)
            
            points.append((lat, lng))
    
    # Add some random points to fill any gaps
    remaining_points = num_points - len(points)
    if remaining_points > 0:
        for _ in range(remaining_points):
            # Random angle
            angle = 2 * math.pi * random.random()
            # Random radius (0 to 1)
            radius_factor = random.random()
            
            # Calculate the point coordinates
            lat = center_lat + lat_degree_radius * radius_factor * math.sin(angle)
            lng = center_lng + lng_degree_radius * radius_factor * math.cos(angle)
            
            points.append((lat, lng))
    
    return points

def generate_population_weighted_points(bounds, num_points):
    """
    Generate points weighted towards populated areas.
    
    In a real application, you would use population density data.
    This is a simplified version that simulates population density.
    
    Args:
        bounds: Tuple of (min_lat, min_lng, max_lat, max_lng)
        num_points: Number of points to generate
    
    Returns:
        List of (lat, lng) tuples
    """
    min_lat, min_lng, max_lat, max_lng = bounds
    
    # Generate a larger number of random points
    candidate_points = []
    for _ in range(num_points * 3):
        lat = min_lat + random.random() * (max_lat - min_lat)
        lng = min_lng + random.random() * (max_lng - min_lng)
        candidate_points.append((lat, lng))
    
    # Use K-means clustering to simulate population centers
    if len(candidate_points) > num_points:
        # Convert to numpy array for K-means
        points_array = np.array(candidate_points)
        
        # Apply K-means clustering
        kmeans = KMeans(n_clusters=num_points, random_state=0).fit(points_array)
        
        # Use the cluster centers as our points
        return [(center[0], center[1]) for center in kmeans.cluster_centers_]
    
    return candidate_points

# Replace the google_maps_extractor function with this improved version
def google_maps_extractor(search_query, location, num_results=10, max_pages=None):
    global progress_info, skipped_businesses
    client = get_gmaps_client()
    businesses = []
    skipped_count = 0
    
    # Calculate dynamic max_pages based on the number of results requested
    if max_pages is None or max_pages == 0:
        max_pages = calculate_dynamic_max_pages(num_results)
    
    progress_info["debug_info"] = f"Using dynamic max pages per website: {max_pages if max_pages is not None else 'unlimited'}"
    
    # For large result sets, we need to use multiple search strategies
    search_strategies = [
        # Strategy 1: Direct search with the original query
        lambda loc: client.places(query=search_query, location=loc),
        
        # Strategy 2: Search with "business" added to the query
        lambda loc: client.places(query=f"{search_query} business", location=loc),
        
        # Strategy 3: Search with location name in the query
        lambda loc: client.places(query=f"{search_query} in {loc[0]},{loc[1]}", location=loc),
        
        # Strategy 4: Nearby search with radius
        lambda loc: client.places_nearby(location=loc, radius=5000, keyword=search_query),
        
        # Strategy 5: Nearby search with larger radius
        lambda loc: client.places_nearby(location=loc, radius=10000, keyword=search_query),
        
        # Strategy 6: Nearby search with different type
        lambda loc: client.places_nearby(location=loc, radius=5000, type="business", keyword=search_query),
        
        # Strategy 7: Search with "company" added to the query
        lambda loc: client.places(query=f"{search_query} company", location=loc),
        
        # Strategy 8: Search with "service" added to the query
        lambda loc: client.places(query=f"{search_query} service", location=loc),
        
        # Strategy 9: Search with "shop" added to the query
        lambda loc: client.places(query=f"{search_query} shop", location=loc),
        
        # Strategy 10: Search with "store" added to the query
        lambda loc: client.places(query=f"{search_query} store", location=loc),
        
        # Strategy 11: Nearby search with even larger radius
        lambda loc: client.places_nearby(location=loc, radius=20000, keyword=search_query),
        
        # Strategy 12: Nearby search with largest radius
        lambda loc: client.places_nearby(location=loc, radius=50000, keyword=search_query)
    ]
    
    # Keep track of all place IDs to avoid duplicates
    processed_place_ids = set()
    
    # Generate initial search points
    initial_search_points = generate_adaptive_search_points(location, num_results)
    
    # Add the original location as the first one to search
    all_locations = [location] + initial_search_points
    
    # Track pagination
    page_count = 0
    max_google_pages = 50  # Increased from 20 to 50 for more results
    
    # Continue searching until we have enough results
    progress_info["debug_info"] = f"Starting search for {num_results} businesses with emails"
    
    # Variables for dynamic expansion
    expansion_count = 0
    max_expansions = 5  # Maximum number of times to expand the search area
    
    # Try each search strategy with each location until we get enough results
    while len(businesses) < num_results and expansion_count <= max_expansions:
        # Check if the extraction has been stopped
        if progress_info["stopped"]:
            progress_info["debug_info"] = "Extraction stopped manually. Saving collected data."
            break
            
        # If we've gone through all locations and still don't have enough results, expand the search area
        if expansion_count > 0:
            progress_info["debug_info"] = f"Expanding search area (expansion {expansion_count}/{max_expansions})"
            
            # Calculate a larger radius for this expansion
            expansion_radius = 50 * (2 ** expansion_count)  # Exponential growth: 50km, 100km, 200km, 400km, 800km
            
            # Generate new search points with the expanded radius
            new_points = generate_radius_based_points(
                location[0], location[1], 
                expansion_radius, 
                min(500, num_results * 2)
            )
            
            # Add the new points to our search locations
            all_locations.extend(new_points)
            
            progress_info["debug_info"] = f"Added {len(new_points)} new search points with radius {expansion_radius}km"
        
        for location_index, current_location in enumerate(all_locations):
            # Check if the extraction has been stopped
            if progress_info["stopped"]:
                break
                
            if len(businesses) >= num_results:
                break
                
            # Skip locations we've already searched in previous iterations
            if location_index < expansion_count * 500 and expansion_count > 0:
                continue
                
            progress_info["debug_info"] = f"Searching location {location_index + 1}/{len(all_locations)}"
            
            for strategy_index, strategy in enumerate(search_strategies):
                # Check if the extraction has been stopped
                if progress_info["stopped"]:
                    break
                    
                if len(businesses) >= num_results:
                    break
                    
                try:
                    progress_info["debug_info"] = f"Location {location_index + 1}, Strategy {strategy_index + 1}"
                    places_result = strategy(current_location)
                    
                    # Process results from this strategy
                    while len(businesses) < num_results and places_result.get('results') and page_count < max_google_pages:
                        # Check if the extraction has been stopped
                        if progress_info["stopped"]:
                            break
                            
                        page_count += 1
                        progress_info["debug_info"] = f"Processing Google Maps page {page_count} (Location {location_index + 1}, Strategy {strategy_index + 1})"
                        
                        for place in places_result['results']:
                            # Check if the extraction has been stopped
                            if progress_info["stopped"]:
                                break
                                
                            place_id = place.get('place_id')
                            
                            # Skip if we've already processed this place
                            if place_id in processed_place_ids:
                                continue
                                
                            processed_place_ids.add(place_id)
                            
                            details = get_business_details(place_id)
                            website = details.get('website', '')
                            
                            # Skip businesses without a website
                            if not website:
                                skipped_count += 1
                                progress_info["skipped"] = skipped_count
                                # Track skipped business with all details
                                skipped_data = create_business_data_dict(details, include_email=False, reason='No website available')
                                skipped_businesses.append(skipped_data)
                                continue
            
                            progress_info["debug_info"] = f"Crawling website: {website}"
                            emails = extract_emails_from_website(website, max_pages=max_pages)
                            
                            if not emails:
                                skipped_count += 1
                                progress_info["skipped"] = skipped_count
                                # Track skipped business with all details
                                skipped_data = create_business_data_dict(details, include_email=False, reason='No emails found on website')
                                skipped_businesses.append(skipped_data)
                                continue
                                
                            business_data = create_business_data_dict(details, include_email=True, email=', '.join(emails))
                            
                            businesses.append(business_data)
                            
                            # Update progress after processing a business
                            progress_info["current"] = len(businesses)
                            progress_info["last_business"] = business_data["Name"]
                            
                            # Small delay to avoid rate limiting
                            sleep(0.5)
                            
                            if len(businesses) >= num_results:
                                break
                        
                        # Check if we need to get more results and if there's a next page token
                        if len(businesses) < num_results and 'next_page_token' in places_result and not progress_info["stopped"]:
                            # Wait for the token to become valid (Google requires a delay)
                            sleep(2)
                            try:
                                places_result = client.places(page_token=places_result['next_page_token'])
                            except Exception as e:
                                logger.error(f"Error in pagination: {str(e)}")
                                progress_info["debug_info"] = f"Pagination error: {str(e)}"
                                break
                        else:
                            break
                            
                except Exception as e:
                    logger.error(f"Error in search strategy {strategy_index + 1}: {str(e)}")
                    progress_info["debug_info"] = f"Error in strategy {strategy_index + 1}: {str(e)}"
                    continue
        
        # If we still don't have enough results and haven't been stopped, increment the expansion counter
        if len(businesses) < num_results and not progress_info["stopped"]:
            expansion_count += 1
            progress_info["debug_info"] = f"Completed search iteration {expansion_count}. Found {len(businesses)}/{num_results} businesses with emails."
    
    # Final status update
    if progress_info["stopped"]:
        progress_info["debug_info"] = f"Extraction stopped manually. Found {len(businesses)} businesses with emails."
    elif len(businesses) < num_results:
        progress_info["debug_info"] = f"Exhausted all search strategies and locations after {expansion_count} expansions. Found {len(businesses)} businesses with emails out of {num_results} requested."
    else:
        progress_info["debug_info"] = f"Successfully found {len(businesses)} businesses with emails as requested after {expansion_count} expansions."
    
    return businesses

# Modify the extraction_task function to reset the stopped flag
def extraction_task(search_query, location, num_results, max_pages):
    global progress_info, skipped_businesses
    # Initialize progress tracker
    progress_info["total"] = num_results
    progress_info["current"] = 0
    progress_info["last_business"] = ""
    progress_info["complete"] = False
    progress_info["error"] = ""
    progress_info["skipped"] = 0
    progress_info["pages_crawled"] = 0
    progress_info["debug_info"] = "Starting extraction..."
    progress_info["stopped"] = False  # Reset the stopped flag
    
    # Reset skipped businesses list
    skipped_businesses = []
    
    try:
        # For large result sets, use a more aggressive approach
        if num_results > 100:
            progress_info["debug_info"] = "Large result set detected. Using aggressive search strategy."
            
        data = google_maps_extractor(search_query, location, num_results, max_pages)
        output_file = "business_data.csv"
        save_to_csv(data, output_file)
        
        # Save skipped businesses
        skipped_file = "skipped_businesses.csv"
        save_skipped_to_csv(skipped_businesses, skipped_file)
        
        if progress_info["stopped"]:
            progress_info["debug_info"] = f"Extraction stopped manually. Saved {len(data)} businesses with emails and {len(skipped_businesses)} skipped businesses."
        elif len(data) < num_results:
            progress_info["debug_info"] = f"Could only find {len(data)} businesses with emails out of {num_results} requested. Tried all search strategies and locations. Skipped {len(skipped_businesses)} businesses."
        else:
            progress_info["debug_info"] = f"Extraction complete. Found {len(data)} businesses with emails as requested. Skipped {len(skipped_businesses)} businesses."
    except Exception as e:
        logger.error(f"Error in extraction task: {str(e)}")
        progress_info["error"] = str(e)
    progress_info["complete"] = True

# Add a new route to handle the stop request
@app.route("/stop_extraction")
def stop_extraction():
    global progress_info
    progress_info["stopped"] = True
    progress_info["debug_info"] = "Stopping extraction... Please wait while we save the collected data."
    return jsonify({"status": "stopping"})

# Add a new function to calculate dynamic max pages based on search progress
def calculate_dynamic_max_pages_based_on_progress(current_results, target_results, current_max_pages):
    global processed_place_ids
    """
    Dynamically adjust the max_pages value based on search progress.
    If we're struggling to find enough businesses with emails, increase the crawl depth.
    
    Args:
        current_results: Number of businesses with emails found so far
        target_results: Total number of businesses with emails requested
        current_max_pages: Current max_pages value
    
    Returns:
        Updated max_pages value
    """
    # If we have no max pages limit, keep it that way
    if current_max_pages is None:
        return None
        
    # Calculate progress percentage
    progress_percentage = current_results / target_results if target_results > 0 else 0
    
    # If we're less than 50% of the way there and have searched at least 100 locations,
    # increase the max_pages to crawl deeper
    if progress_percentage < 0.5 and len(processed_place_ids) > 100:
        # Increase by 50%
        new_max_pages = int(current_max_pages * 1.5)
        progress_info["debug_info"] = f"Increasing max pages per website from {current_max_pages} to {new_max_pages} to find more emails"
        return new_max_pages
    
    # If we're less than 80% of the way there and have searched at least 200 locations,
    # increase even more
    if progress_percentage < 0.8 and len(processed_place_ids) > 200:
        # Double it
        new_max_pages = current_max_pages * 2
        progress_info["debug_info"] = f"Significantly increasing max pages per website from {current_max_pages} to {new_max_pages} to find more emails"
        return new_max_pages
    
    return current_max_pages

# Add this to the extraction_task function right before calling google_maps_extractor
def extraction_task(search_query, location, num_results, max_pages):
    global progress_info, skipped_businesses
    # Initialize progress tracker
    progress_info["total"] = num_results
    progress_info["current"] = 0
    progress_info["last_business"] = ""
    progress_info["complete"] = False
    progress_info["error"] = ""
    progress_info["skipped"] = 0
    progress_info["pages_crawled"] = 0
    progress_info["debug_info"] = "Starting extraction..."
    
    # Reset skipped businesses list
    skipped_businesses = []
    
    try:
        # For large result sets, use a more aggressive approach
        if num_results > 100:
            progress_info["debug_info"] = "Large result set detected. Using aggressive search strategy."
            
        data = google_maps_extractor(search_query, location, num_results, max_pages)
        output_file = "business_data.csv"
        save_to_csv(data, output_file)
        
        # Save skipped businesses
        skipped_file = "skipped_businesses.csv"
        save_skipped_to_csv(skipped_businesses, skipped_file)
        
        if len(data) < num_results:
            progress_info["debug_info"] = f"Could only find {len(data)} businesses with emails out of {num_results} requested. Tried all search strategies and locations. Skipped {len(skipped_businesses)} businesses."
        else:
            progress_info["debug_info"] = f"Extraction complete. Found {len(data)} businesses with emails as requested. Skipped {len(skipped_businesses)} businesses."
    except Exception as e:
        logger.error(f"Error in extraction task: {str(e)}")
        progress_info["error"] = str(e)
    progress_info["complete"] = True

# -------------------- Flask Routes --------------------

@app.route("/", methods=["GET", "POST"])
def index():
    global progress_info
    # Reset progress if the "reset" query parameter is present
    if request.method == "GET" and request.args.get("reset"):
        progress_info = {
            "current": 0,
            "total": 0,
            "last_business": "",
            "complete": False,
            "error": "",
            "skipped": 0,
            "pages_crawled": 0,
            "debug_info": "",
            "stopped": False
        }
    if request.method == "POST":
        if not API_KEY:
            flash("API key is not set. Please set it via the setuppage first.")
            return redirect(url_for("index"))
            
        search_query = request.form.get("search_query", "hotels")
        latitude = request.form.get("latitude", "37.7749")
        longitude = request.form.get("longitude", "-122.4194")
        try:
            num_results = int(request.form.get("num_results", "10"))
            max_pages = int(request.form.get("max_pages", "0")) if request.form.get("max_pages") else 0
            lat = float(latitude)
            lng = float(longitude)
        except Exception as e:
            flash("Invalid input data. Please check your entries.")
            return redirect(url_for("index"))
        
        location = (lat, lng)
        
        # Start extraction in a background thread
        extraction_thread = threading.Thread(
            target=extraction_task,
            args=(search_query, location, num_results, max_pages)
        )
        extraction_thread.daemon = True  # Make thread a daemon so it exits when the main thread exits
        extraction_thread.start()
        
        flash("Extraction started! You can watch the progress at the bottom of the page.", "info")
        return redirect(url_for("index"))
        
    return render_template("index.html")


@app.route("/progress")
def progress():
    return jsonify(progress_info)

@app.route("/result")
def result():
    return render_template("result.html")

@app.route("/download")
def download():
    file_path = os.path.join(os.getcwd(), "business_data.csv")
    return send_file(file_path, as_attachment=True)

@app.route("/download_skipped")
def download_skipped():
    file_path = os.path.join(os.getcwd(), "skipped_businesses.csv")
    return send_file(file_path, as_attachment=True)

@app.route("/setuppage", methods=["GET", "POST"])
def setuppage():
    global API_KEY
    if request.method == "POST":
        new_api_key = request.form.get("api_key")
        if new_api_key:
            try:
                test_client = googlemaps.Client(key=new_api_key)
            except Exception as e:
                flash("Invalid API key provided. Please try again.", "error")
                return redirect(url_for("setuppage"))
            API_KEY = new_api_key
            flash("API key updated!", "success")
        return redirect(url_for("setuppage"))
    return render_template("setuppage.html", api_key=API_KEY)

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000, debug=True)

