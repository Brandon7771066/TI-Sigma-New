"""
POLAR H10 PULSOID RECEIVER
===========================
Receives real-time heart rate data from Polar H10 via Pulsoid API.

SETUP:
1. Download Pulsoid app on your phone (iOS/Android)
2. Create free account at pulsoid.net
3. Pair your Polar H10 in the app
4. Get API token from: https://pulsoid.net/ui/keys
5. Set PULSOID_TOKEN environment variable or paste token below

This streams HR data and calculates:
- Heart Rate Variability (HRV) 
- Coherence score (for LCC testing)
- Real-time LCC training feedback
"""

import os
import time
import json
import requests
import numpy as np
from datetime import datetime
from collections import deque
import csv

PULSOID_API_URL = "https://dev.pulsoid.net/api/v1/data/heart_rate/latest"

class PolarH10PulsoidReceiver:
    """
    Receives HR data from Polar H10 via Pulsoid cloud service.
    """
    
    def __init__(self, token: str = None, goal_hr: int = 65):
        self.token = token or os.environ.get('PULSOID_TOKEN')
        if not self.token:
            raise ValueError("PULSOID_TOKEN required! Get one at https://pulsoid.net/ui/keys")
        
        self.headers = {
            "Authorization": f"Bearer {self.token}",
            "Content-Type": "application/json"
        }
        
        self.goal_hr = goal_hr
        self.hr_buffer = deque(maxlen=60)
        self.rr_intervals = deque(maxlen=120)
        self.session_data = []
        self.start_time = None
        self.coherence_history = deque(maxlen=30)
        
    def get_heart_rate(self) -> dict:
        """Fetch latest heart rate from Pulsoid API"""
        try:
            response = requests.get(PULSOID_API_URL, headers=self.headers, timeout=5)
            if response.status_code == 200:
                data = response.json()
                return {
                    'hr': data.get('data', {}).get('heart_rate', 0),
                    'measured_at': data.get('data', {}).get('measured_at', ''),
                    'success': True
                }
            else:
                return {'success': False, 'error': f"API error: {response.status_code}"}
        except Exception as e:
            return {'success': False, 'error': str(e)}
    
    def calculate_hrv(self) -> dict:
        """Calculate Heart Rate Variability metrics"""
        if len(self.hr_buffer) < 10:
            return {'rmssd': 0, 'sdnn': 0, 'valid': False}
        
        hrs = list(self.hr_buffer)
        rr_from_hr = [60000 / hr for hr in hrs if hr > 0]
        
        if len(rr_from_hr) < 5:
            return {'rmssd': 0, 'sdnn': 0, 'valid': False}
        
        diffs = np.diff(rr_from_hr)
        rmssd = np.sqrt(np.mean(diffs ** 2))
        
        sdnn = np.std(rr_from_hr)
        
        return {
            'rmssd': rmssd,
            'sdnn': sdnn,
            'mean_rr': np.mean(rr_from_hr),
            'valid': True
        }
    
    def calculate_coherence(self) -> float:
        """
        Calculate heart-brain coherence score.
        Based on HRV pattern analysis - higher coherence = more ordered heart rhythm.
        """
        hrv = self.calculate_hrv()
        if not hrv['valid']:
            return 0.0
        
        hrs = list(self.hr_buffer)
        if len(hrs) < 10:
            return 0.0
        
        amplitude = np.std(hrs)
        regularity = 1.0 / (1.0 + np.std(np.diff(hrs)))
        
        if hrv['rmssd'] > 0:
            hrv_quality = min(1.0, hrv['rmssd'] / 50.0)
        else:
            hrv_quality = 0.0
        
        coherence = (amplitude * 0.3 + regularity * 0.4 + hrv_quality * 0.3) * 100
        coherence = min(100, max(0, coherence))
        
        return coherence
    
    def calculate_lcc_distance(self) -> float:
        """
        Calculate LCC distance from goal state.
        For HR, we measure distance from optimal relaxed/coherent state.
        """
        if len(self.hr_buffer) < 5:
            return 1.0
        
        current_hr = np.mean(list(self.hr_buffer)[-5:])
        
        hr_distance = abs(current_hr - self.goal_hr) / 40.0
        
        coherence = self.calculate_coherence()
        coherence_distance = (100 - coherence) / 100.0
        
        lcc_distance = (hr_distance * 0.4 + coherence_distance * 0.6)
        return min(1.0, lcc_distance)
    
    def stream(self, duration_seconds: int = 300, save_file: str = None):
        """
        Stream heart rate data for LCC testing.
        
        Args:
            duration_seconds: How long to stream (default 5 minutes)
            save_file: Optional CSV file to save data
        """
        print("\n" + "="*60)
        print("🫀 POLAR H10 LCC TRAINING SESSION")
        print("="*60)
        print(f"Goal HR: {self.goal_hr} BPM")
        print(f"Duration: {duration_seconds} seconds")
        print("\nConnecting to Pulsoid...")
        
        test = self.get_heart_rate()
        if not test['success']:
            print(f"\n❌ Connection failed: {test['error']}")
            print("\nTroubleshooting:")
            print("1. Make sure Pulsoid app is running on your phone")
            print("2. Ensure Polar H10 is connected in the app")
            print("3. Check your API token is correct")
            return
        
        print(f"✅ Connected! Initial HR: {test['hr']} BPM")
        print("\n" + "-"*60)
        print("LIVE LCC TRAINING")
        print("-"*60)
        
        self.start_time = time.time()
        
        if save_file:
            csvfile = open(save_file, 'w', newline='')
            writer = csv.writer(csvfile)
            writer.writerow(['timestamp', 'hr', 'coherence', 'lcc_distance', 'hrv_rmssd'])
        
        try:
            while time.time() - self.start_time < duration_seconds:
                data = self.get_heart_rate()
                
                if data['success'] and data['hr'] > 0:
                    hr = data['hr']
                    self.hr_buffer.append(hr)
                    
                    coherence = self.calculate_coherence()
                    self.coherence_history.append(coherence)
                    lcc_distance = self.calculate_lcc_distance()
                    hrv = self.calculate_hrv()
                    
                    distance_to_goal = abs(hr - self.goal_hr)
                    if distance_to_goal < 5:
                        bar = "🟢" * 10
                        status = "PERFECT!"
                    elif distance_to_goal < 10:
                        bar = "🟡" * 7 + "⬜" * 3
                        status = "CLOSE"
                    elif distance_to_goal < 15:
                        bar = "🟠" * 5 + "⬜" * 5
                        status = "ADJUSTING"
                    else:
                        bar = "🔴" * 3 + "⬜" * 7
                        status = "BREATHE..."
                    
                    elapsed = int(time.time() - self.start_time)
                    print(f"\r[{elapsed:3d}s] HR: {hr:3d} | Coherence: {coherence:5.1f}% | LCC: {lcc_distance:.3f} | {bar} {status}    ", end='', flush=True)
                    
                    record = {
                        'timestamp': datetime.now().isoformat(),
                        'hr': hr,
                        'coherence': coherence,
                        'lcc_distance': lcc_distance,
                        'hrv_rmssd': hrv['rmssd'] if hrv['valid'] else 0
                    }
                    self.session_data.append(record)
                    
                    if save_file:
                        writer.writerow([
                            record['timestamp'],
                            record['hr'],
                            record['coherence'],
                            record['lcc_distance'],
                            record['hrv_rmssd']
                        ])
                        csvfile.flush()
                
                time.sleep(1)
                
        except KeyboardInterrupt:
            print("\n\nSession stopped by user.")
        finally:
            if save_file:
                csvfile.close()
        
        self._print_summary()
        return self.session_data
    
    def _print_summary(self):
        """Print session summary with LCC analysis"""
        if not self.session_data:
            print("\nNo data collected.")
            return
        
        hrs = [d['hr'] for d in self.session_data]
        coherences = [d['coherence'] for d in self.session_data]
        lcc_distances = [d['lcc_distance'] for d in self.session_data]
        
        print("\n\n" + "="*60)
        print("📊 SESSION SUMMARY")
        print("="*60)
        
        print(f"\n📈 Heart Rate:")
        print(f"   Average: {np.mean(hrs):.1f} BPM")
        print(f"   Min: {np.min(hrs)} BPM")
        print(f"   Max: {np.max(hrs)} BPM")
        print(f"   Std Dev: {np.std(hrs):.1f}")
        
        print(f"\n🧠 Coherence:")
        print(f"   Average: {np.mean(coherences):.1f}%")
        print(f"   Peak: {np.max(coherences):.1f}%")
        print(f"   Time in high coherence (>50%): {np.sum(np.array(coherences) > 50) / len(coherences) * 100:.1f}%")
        
        print(f"\n🎯 LCC Distance:")
        print(f"   Average: {np.mean(lcc_distances):.3f}")
        print(f"   Best (min): {np.min(lcc_distances):.3f}")
        print(f"   Time near goal (<0.3): {np.sum(np.array(lcc_distances) < 0.3) / len(lcc_distances) * 100:.1f}%")
        
        first_half = lcc_distances[:len(lcc_distances)//2]
        second_half = lcc_distances[len(lcc_distances)//2:]
        improvement = np.mean(first_half) - np.mean(second_half)
        
        if improvement > 0:
            print(f"\n✅ IMPROVEMENT: LCC distance decreased by {improvement:.3f} ({improvement/np.mean(first_half)*100:.1f}%)")
            print("   Your heart rhythm is responding to the training!")
        else:
            print(f"\n📊 LCC distance changed by {improvement:.3f}")
        
        print("\n" + "="*60)


def test_connection():
    """Quick test to verify Pulsoid connection"""
    token = os.environ.get('PULSOID_TOKEN')
    if not token:
        print("❌ PULSOID_TOKEN not set!")
        print("\nTo set up:")
        print("1. Go to https://pulsoid.net/ui/keys")
        print("2. Create a new API token")
        print("3. Set it as PULSOID_TOKEN secret in Replit")
        return False
    
    receiver = PolarH10PulsoidReceiver(token)
    result = receiver.get_heart_rate()
    
    if result['success']:
        print(f"✅ Connected! Current HR: {result['hr']} BPM")
        return True
    else:
        print(f"❌ Connection failed: {result['error']}")
        return False


if __name__ == "__main__":
    import sys
    
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        test_connection()
    else:
        receiver = PolarH10PulsoidReceiver(goal_hr=65)
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        save_path = f"attached_assets/polar_h10_lcc_{timestamp}.csv"
        
        receiver.stream(duration_seconds=300, save_file=save_path)
