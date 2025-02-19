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
    "error": ""
}

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
    place_details = client.place(place_id=place_id, fields=fields)
    return place_details.get('result', {})

INVALID_TLDS = {
    'png', 'jpg', 'jpeg', 'gif', 'svg', 'webp', 'bmp', 'ico', 'tiff',
    'css', 'js', 'pdf', 'doc', 'docx', 'xls', 'xlsx', 'ppt', 'pptx', 'zip'
}

def crawl_website_for_emails(start_url, max_pages=20):
    """
    Crawl the website starting from start_url, following internal links up to max_pages,
    and extract email addresses from all pages.
    """
    visited = set()
    emails = set()
    to_visit = [start_url]
    parsed_base = urlparse(start_url)
    base_domain = parsed_base.netloc

    while to_visit and len(visited) < max_pages:
        current_url = to_visit.pop(0)
        if current_url in visited:
            continue
        visited.add(current_url)
        try:
            response = requests.get(current_url, timeout=10)
            if response.status_code != 200:
                continue
            html_content = response.text

            # Extract emails from current page
            found_emails = re.findall(
                r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b',
                html_content,
                re.IGNORECASE
            )
            for email in found_emails:
                domain_part = email.split('@')[-1].lower()
                tld = domain_part.split('.')[-1]
                if tld not in INVALID_TLDS:
                    emails.add(email)

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
            continue

    return emails

def extract_emails_from_website(url, max_pages=20):
    """
    Extract email addresses by deeply crawling the website for all its contents.
    If the provided URL is not the homepage, the homepage is used as the starting point.
    """
    parsed_url = urlparse(url)
    homepage_url = f"{parsed_url.scheme}://{parsed_url.netloc}"
    emails = crawl_website_for_emails(homepage_url, max_pages=max_pages)
    return list(emails)

def get_country_from_formatted_address(formatted_address):
    """Extract the country from a formatted address string.
    
    Assumes that the country is the last element after splitting by comma.
    """
    if not formatted_address:
        return ''
    parts = formatted_address.split(',')
    return parts[-1].strip() if parts else ''


def google_maps_extractor(search_query, location, num_results=10, max_pages=20):
    global progress_info
    client = get_gmaps_client()
    businesses = []
    
    # Initial search
    places_result = client.places(query=search_query, location=location)
    
    while len(businesses) < num_results and places_result.get('results'):
        for place in places_result['results']:
            if len(businesses) >= num_results:
                break
                
            details = get_business_details(place['place_id'])
            website = details.get('website', '')
            # Skip businesses without a website
            if not website:
                continue

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
                'Coordinates': '',
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
                'Website': website,
                'Photo': str(details.get('photo', '')),
                'Business Status': details.get('business_status', ''),
                'Serves Beer': details.get('serves_beer', ''),
                'Review': str(details.get('review', '')),
                'Formatted Address': details.get('formatted_address', ''),
                'Serves Dinner': details.get('serves_dinner', ''),
                'Wheelchair Accessible Entrance': details.get('wheelchair_accessible_entrance', ''),
                'Country': get_country_from_formatted_address(details.get('formatted_address', '')),
                'Email': ''
            }
            
            if 'geometry' in details and 'location' in details['geometry']:
                loc = details['geometry']['location']
                business_data['Coordinates'] = f"{loc.get('lat', '')}, {loc.get('lng', '')}"
            
            emails = extract_emails_from_website(website, max_pages=max_pages)
            if not emails:
                continue
            business_data['Email'] = ', '.join(emails)
            
            businesses.append(business_data)
            
            # Update progress after processing a business
            progress_info["current"] = len(businesses)
            progress_info["last_business"] = business_data["Name"]
            
            sleep(0.5)  # small delay for demonstration
        
        if 'next_page_token' in places_result:
            sleep(2)  # Wait for the token to become valid
            places_result = client.places(query=search_query, page_token=places_result['next_page_token'])
        else:
            break
    
    return businesses

def save_to_csv(data, filename):
    """Save extracted data to CSV file"""
    fieldnames = [
        'Name', 'Email', 'Website', 'Formatted Phone Number','Formatted Address', 'Place ID',
        'Delivery', 'Opening Hours', 'Serves Brunch', 'Rating', 'Editorial Summary',
        'Serves Breakfast', 'International Phone Number', 'User Ratings Total', 'Curbside Pickup',
        'Plus Code', 'Vicinity', 'Coordinates', 'Serves Vegetarian Food', 'Takeout', 'Price Level',
        'Dine In', 'Serves Lunch', 'Icon', 'Reservable', 'URL', 'Type', 'Reviews', 'Serves Wine',
        'ADR Address', 'Permanently Closed', 'UTC Offset', 'Current Opening Hours',
        'Secondary Opening Hours', 'Photo', 'Business Status', 'Serves Beer', 'Review',
        'Serves Dinner', 'Wheelchair Accessible Entrance', 'Country'
    ]
    with open(filename, 'w', newline='', encoding='utf-8') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()
        for business in data:
            writer.writerow(business)

def extraction_task(search_query, location, num_results, max_pages):
    global progress_info
    # Initialize progress tracker
    progress_info["total"] = num_results
    progress_info["current"] = 0
    progress_info["last_business"] = ""
    progress_info["complete"] = False
    progress_info["error"] = ""
    
    try:
        data = google_maps_extractor(search_query, location, num_results, max_pages)
        output_file = "business_data.csv"
        save_to_csv(data, output_file)
    except Exception as e:
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
            "error": ""
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
            max_pages = int(request.form.get("max_pages", "20"))
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

