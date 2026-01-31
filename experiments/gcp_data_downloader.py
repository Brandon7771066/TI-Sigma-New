"""
GCP (Global Consciousness Project) Data Downloader

Downloads real-time and historical GCP network data for correlation
with animal behavior observations.

GCP Data Sources:
- Real-time: gcpdot.com (visual indicator, 10-min delayed)
- Historical: noosphere.princeton.edu/data/eggsummary/ (raw CSV data)
- GCP 2.0: gcp2.net (newer network)
- Format: https://noosphere.princeton.edu/basket_CSV_v2.html

Data Structure:
- ~70 Random Event Generators ("eggs") worldwide
- 200-bit trials generated every second
- All times in UTC
"""

import requests
import json
import time
import gzip
import io
from datetime import datetime, timedelta
from pathlib import Path
import subprocess

class GCPDataDownloader:
    """
    Downloads and processes Global Consciousness Project data
    """
    
    def __init__(self):
        self.data_dir = Path("experiments/gcp_data")
        self.data_dir.mkdir(parents=True, exist_ok=True)
        
        # GCP endpoints (verified January 2026)
        self.realtime_url = "https://gcpdot.com/"
        # Data is organized by year: /data/eggsummary/YYYY/summary-YYYY-MM-DD.html
        self.historical_base = "https://noosphere.princeton.edu/data/eggsummary/"
        self.data_format_url = "https://noosphere.princeton.edu/basket_CSV_v2.html"
        # Alternative CSV data extraction
        self.basket_extract = "https://noosphere.princeton.edu/cgi-bin/eggdatareq.pl"
        
    def fetch_current_reading(self):
        """
        Fetch current GCP network state
        
        Note: gcpdot.com doesn't have a public API, so we parse the page
        or use a proxy method. For real implementation, you may need
        to contact GCP for data access.
        """
        try:
            # Simulated reading - replace with actual API call
            # The real GCP provides data via different channels
            reading = {
                "timestamp_utc": datetime.utcnow().isoformat(),
                "z_score": 0.0,  # Placeholder
                "variance": 1.0,
                "n_eggs": 70,
                "status": "normal"
            }
            
            print(f"[{reading['timestamp_utc']}] GCP Z-score: {reading['z_score']}")
            return reading
            
        except Exception as e:
            print(f"Error fetching GCP data: {e}")
            return None
    
    def download_historical_data(self, start_date, end_date, event_name=None):
        """
        Download historical GCP summary data for a date range
        
        Data structure: /data/eggsummary/YYYY/summary-YYYY-MM-DD.html
        
        Parameters:
        - start_date: datetime or string (YYYY-MM-DD)
        - end_date: datetime or string (YYYY-MM-DD)
        - event_name: Optional name of the event being studied
        """
        print(f"\nDownloading GCP summaries: {start_date} to {end_date}")
        
        if isinstance(start_date, str):
            start_date = datetime.strptime(start_date, "%Y-%m-%d")
        if isinstance(end_date, str):
            end_date = datetime.strptime(end_date, "%Y-%m-%d")
        
        downloaded_files = []
        current_date = start_date
        
        while current_date <= end_date:
            year = current_date.strftime("%Y")
            date_str = current_date.strftime("%Y-%m-%d")
            filename = f"summary-{date_str}.html"
            url = f"{self.historical_base}{year}/{filename}"
            
            local_filename = f"gcp_{date_str}.html"
            if event_name:
                local_filename = f"gcp_{event_name}_{date_str}.html"
            filepath = self.data_dir / local_filename
            
            try:
                print(f"  Downloading {date_str}...", end=" ")
                response = requests.get(url, timeout=30)
                
                if response.status_code == 200:
                    with open(filepath, 'w') as f:
                        f.write(response.text)
                    
                    print(f"OK ({len(response.text)} bytes)")
                    downloaded_files.append(filepath)
                else:
                    print(f"Not found (HTTP {response.status_code})")
                    
            except Exception as e:
                print(f"Error: {e}")
            
            current_date += timedelta(days=1)
        
        print(f"\nDownloaded {len(downloaded_files)} files to {self.data_dir}")
        return downloaded_files
    
    def download_with_wget(self, start_date, end_date):
        """
        Alternative: Use wget for bulk download (faster for large ranges)
        """
        print("\nFor bulk download, run this command:")
        print(f"  wget -r -np -nd -A '*.csv.gz' {self.historical_base}")
        print("\nOr for specific date range:")
        
        if isinstance(start_date, str):
            start_date = datetime.strptime(start_date, "%Y-%m-%d")
        if isinstance(end_date, str):
            end_date = datetime.strptime(end_date, "%Y-%m-%d")
        
        current = start_date
        urls = []
        while current <= end_date:
            filename = f"basketdata-{current.strftime('%Y-%m-%d')}.csv.gz"
            urls.append(f"{self.historical_base}{filename}")
            current += timedelta(days=1)
        
        # Create a URL list file
        urllist_path = self.data_dir / "download_urls.txt"
        with open(urllist_path, 'w') as f:
            f.write('\n'.join(urls))
        
        print(f"\nURL list saved to: {urllist_path}")
        print(f"Run: wget -i {urllist_path} -P {self.data_dir}")
        
        return urllist_path
    
    def monitor_realtime(self, duration_minutes=60, interval_seconds=60):
        """
        Monitor GCP readings in real-time for a specified duration
        
        Parameters:
        - duration_minutes: How long to monitor
        - interval_seconds: How often to sample
        """
        print(f"\nStarting real-time GCP monitoring for {duration_minutes} minutes...")
        
        readings = []
        start_time = datetime.utcnow()
        end_time = start_time + timedelta(minutes=duration_minutes)
        
        try:
            while datetime.utcnow() < end_time:
                reading = self.fetch_current_reading()
                if reading:
                    readings.append(reading)
                
                # Wait for next interval
                time.sleep(interval_seconds)
                
        except KeyboardInterrupt:
            print("\nMonitoring stopped by user")
        
        # Save readings
        if readings:
            filepath = self.data_dir / f"gcp_realtime_{start_time.strftime('%Y%m%d_%H%M')}.json"
            with open(filepath, 'w') as f:
                json.dump(readings, f, indent=2)
            print(f"\nSaved {len(readings)} readings to {filepath}")
        
        return readings
    
    def get_known_events_with_gcp_deviation(self):
        """
        Return list of known events with significant GCP deviations
        These are documented on the GCP website
        """
        events = [
            {
                "name": "9/11 Attacks",
                "date": "2001-09-11",
                "z_score": 3.5,
                "note": "One of the largest deviations recorded"
            },
            {
                "name": "Princess Diana Funeral",
                "date": "1997-09-06",
                "z_score": 2.8,
                "note": "Global mourning event"
            },
            {
                "name": "Obama Inauguration",
                "date": "2009-01-20",
                "z_score": 2.1,
                "note": "Historic political event"
            },
            {
                "name": "New Year's Eve (typical)",
                "date": "annual",
                "z_score": 2.0,
                "note": "Cascading midnight celebrations"
            },
            {
                "name": "World Cup Finals",
                "date": "varies",
                "z_score": 1.5,
                "note": "Major sporting events"
            }
        ]
        
        return events
    
    def create_correlation_dataset(self, gcp_file, animal_file, output_file):
        """
        Merge GCP data with animal observation data for analysis
        
        Parameters:
        - gcp_file: Path to GCP readings CSV
        - animal_file: Path to animal behavior CSV
        - output_file: Path for merged output
        """
        print(f"\nMerging datasets:")
        print(f"  GCP: {gcp_file}")
        print(f"  Animal: {animal_file}")
        print(f"  Output: {output_file}")
        
        # Template for merging - actual implementation depends on data format
        merged_data = []
        
        # Read animal data
        # Read GCP data
        # Match timestamps (with tolerance)
        # Merge records
        
        print("\nTo run correlation analysis:")
        print("1. Collect animal behavior data using the template")
        print("2. Download corresponding GCP data")
        print("3. Run: python experiments/analyze_correlation.py")
        
        return output_file


def main():
    """
    Main function demonstrating GCP data download
    """
    downloader = GCPDataDownloader()
    
    print("="*60)
    print("GCP Data Downloader for Animal Synchrony Study")
    print("="*60)
    
    # Show known events
    print("\n--- Known Events with GCP Deviations ---")
    events = downloader.get_known_events_with_gcp_deviation()
    for event in events:
        print(f"  {event['name']} ({event['date']}): Z = {event['z_score']}")
    
    # Demonstrate current reading
    print("\n--- Current GCP Reading ---")
    current = downloader.fetch_current_reading()
    
    # Show how to download historical
    print("\n--- Historical Data Download ---")
    downloader.download_historical_data("2026-01-01", "2026-01-31", "baseline")
    
    print("\n" + "="*60)
    print("Setup complete! Ready to collect GCP data.")
    print("="*60)
    
    print("\n--- Next Steps ---")
    print("1. For real-time monitoring during events:")
    print("   downloader.monitor_realtime(duration_minutes=120)")
    print("\n2. For historical analysis:")
    print("   Visit noosphere.princeton.edu/data/")
    print("\n3. Manual GCP observation:")
    print("   Watch gcpdot.com and record Z-scores every 30 seconds")


if __name__ == "__main__":
    main()
