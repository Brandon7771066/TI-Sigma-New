#!/usr/bin/env python3
"""
📤 Mendi Companion Data Uploader
================================

Uploads Mendi fNIRS data to Replit Data Bridge API

Usage Options:
1. Real-time streaming from Mendi app export
2. Batch upload from CSV file
3. Manual data entry for testing

Author: Brandon Emerick
Date: November 23, 2025
"""

import requests
import json
import time
from datetime import datetime
import argparse
import csv
import sys

class MendiUploader:
    def __init__(self, api_url: str):
        """
        Initialize uploader
        
        Args:
            api_url: Base URL of the Data Bridge API
                    e.g., "https://your-repl.replit.app:8000"
        """
        self.api_url = api_url.rstrip('/')
        self.upload_endpoint = f"{self.api_url}/api/mendi/upload"
        self.session_id = f"session-{datetime.now().strftime('%Y%m%d-%H%M%S')}"
        
    def check_health(self):
        """Check if API is reachable"""
        try:
            response = requests.get(f"{self.api_url}/health", timeout=5)
            if response.status_code == 200:
                print("✅ API is healthy!")
                print(f"   {response.json()}")
                return True
            else:
                print(f"⚠️ API returned status {response.status_code}")
                return False
        except Exception as e:
            print(f"❌ Cannot reach API: {e}")
            return False
    
    def upload_sample(self, hbo2: float, hbr: float, 
                     timestamp: str = None,
                     signal_quality: float = 1.0,
                     metadata: dict = None):
        """
        Upload a single fNIRS sample
        
        Args:
            hbo2: Oxygenated hemoglobin (μM)
            hbr: Deoxygenated hemoglobin (μM)
            timestamp: ISO format timestamp (defaults to now)
            signal_quality: 0-1 quality score
            metadata: Additional metadata
        """
        if timestamp is None:
            timestamp = datetime.now().isoformat()
        
        total_hb = hbo2 + hbr
        oxygenation_percent = (hbo2 / total_hb * 100) if total_hb > 0 else 0
        
        payload = {
            'timestamp': timestamp,
            'hbo2': hbo2,
            'hbr': hbr,
            'total_hb': total_hb,
            'oxygenation_percent': oxygenation_percent,
            'signal_quality': signal_quality,
            'device_id': 'mendi-companion-uploader',
            'session_id': self.session_id,
            'metadata': metadata or {}
        }
        
        try:
            response = requests.post(
                self.upload_endpoint,
                json=payload,
                timeout=10
            )
            
            if response.status_code == 201:
                print(f"✅ Uploaded: HbO2={hbo2:.1f}, HbR={hbr:.1f}, Oxy={oxygenation_percent:.1f}%")
                return True
            else:
                print(f"❌ Upload failed: {response.status_code} - {response.text}")
                return False
                
        except Exception as e:
            print(f"❌ Upload error: {e}")
            return False
    
    def upload_batch(self, samples: list):
        """
        Upload multiple samples at once
        
        Args:
            samples: List of dicts with hbo2, hbr, timestamp, etc.
        """
        payload = {'samples': samples}
        
        try:
            response = requests.post(
                self.upload_endpoint,
                json=payload,
                timeout=30
            )
            
            if response.status_code == 201:
                result = response.json()
                print(f"✅ Batch uploaded: {result.get('count', 0)} samples")
                return True
            else:
                print(f"❌ Batch upload failed: {response.status_code} - {response.text}")
                return False
                
        except Exception as e:
            print(f"❌ Batch upload error: {e}")
            return False
    
    def upload_from_csv(self, csv_file: str):
        """
        Upload data from CSV file
        
        Expected CSV columns: timestamp, hbo2, hbr, signal_quality (optional)
        """
        print(f"📁 Reading CSV file: {csv_file}")
        
        samples = []
        with open(csv_file, 'r') as f:
            reader = csv.DictReader(f)
            for row in reader:
                sample = {
                    'timestamp': row.get('timestamp', datetime.now().isoformat()),
                    'hbo2': float(row['hbo2']),
                    'hbr': float(row['hbr']),
                    'signal_quality': float(row.get('signal_quality', 1.0)),
                    'device_id': 'csv-import',
                    'session_id': self.session_id
                }
                
                total_hb = sample['hbo2'] + sample['hbr']
                sample['total_hb'] = total_hb
                sample['oxygenation_percent'] = (sample['hbo2'] / total_hb * 100) if total_hb > 0 else 0
                sample['metadata'] = {'source': 'csv', 'filename': csv_file}
                
                samples.append(sample)
        
        print(f"📊 Found {len(samples)} samples")
        
        # Upload in batches of 100
        batch_size = 100
        for i in range(0, len(samples), batch_size):
            batch = samples[i:i+batch_size]
            print(f"📤 Uploading batch {i//batch_size + 1}...")
            self.upload_batch(batch)
            time.sleep(0.5)  # Rate limiting
        
        print("✅ CSV upload complete!")
    
    def stream_demo_data(self, duration_seconds: int = 60, hz: float = 1.0):
        """
        Stream synthetic demo data for testing
        
        Args:
            duration_seconds: How long to stream
            hz: Samples per second
        """
        print(f"🎬 Streaming demo data for {duration_seconds}s at {hz} Hz...")
        print(f"📊 Session ID: {self.session_id}")
        
        import numpy as np
        
        t = 0
        interval = 1.0 / hz
        
        while t < duration_seconds:
            # Synthetic realistic fNIRS values
            base_hbo2 = 65 + 10 * np.sin(2 * np.pi * t / 30)  # 30s oscillation
            base_hbr = 45 + 5 * np.sin(2 * np.pi * t / 20 + np.pi/4)
            
            # Add noise
            hbo2 = base_hbo2 + np.random.normal(0, 2)
            hbr = base_hbr + np.random.normal(0, 1.5)
            
            # Quality varies
            signal_quality = 0.7 + 0.3 * np.random.random()
            
            self.upload_sample(hbo2, hbr, signal_quality=signal_quality)
            
            time.sleep(interval)
            t += interval
        
        print("✅ Demo streaming complete!")

def main():
    parser = argparse.ArgumentParser(description='Upload Mendi fNIRS data to Replit')
    
    parser.add_argument('--api-url', 
                       default='http://localhost:8000',
                       help='API base URL (default: http://localhost:8000)')
    
    parser.add_argument('--mode', 
                       choices=['demo', 'csv', 'manual'],
                       default='demo',
                       help='Upload mode')
    
    parser.add_argument('--csv-file',
                       help='CSV file to upload (for csv mode)')
    
    parser.add_argument('--duration',
                       type=int,
                       default=60,
                       help='Demo stream duration in seconds (default: 60)')
    
    parser.add_argument('--hz',
                       type=float,
                       default=1.0,
                       help='Demo stream frequency in Hz (default: 1.0)')
    
    args = parser.parse_args()
    
    uploader = MendiUploader(args.api_url)
    
    # Check API health
    if not uploader.check_health():
        print("\n❌ Cannot connect to API. Make sure the Data Bridge API is running!")
        print(f"   Expected URL: {args.api_url}")
        sys.exit(1)
    
    print(f"\n🚀 Starting upload in {args.mode} mode...\n")
    
    if args.mode == 'demo':
        uploader.stream_demo_data(args.duration, args.hz)
    
    elif args.mode == 'csv':
        if not args.csv_file:
            print("❌ Error: --csv-file required for csv mode")
            sys.exit(1)
        uploader.upload_from_csv(args.csv_file)
    
    elif args.mode == 'manual':
        print("📝 Manual mode - Enter data interactively")
        print("   Format: hbo2 hbr (or 'quit' to exit)\n")
        
        while True:
            try:
                user_input = input("Enter HbO2 HbR: ").strip()
                
                if user_input.lower() in ['quit', 'exit', 'q']:
                    break
                
                parts = user_input.split()
                if len(parts) != 2:
                    print("❌ Invalid format. Use: hbo2 hbr")
                    continue
                
                hbo2 = float(parts[0])
                hbr = float(parts[1])
                
                uploader.upload_sample(hbo2, hbr)
                
            except KeyboardInterrupt:
                print("\n\n👋 Goodbye!")
                break
            except ValueError:
                print("❌ Invalid numbers. Use: hbo2 hbr")

if __name__ == '__main__':
    main()
