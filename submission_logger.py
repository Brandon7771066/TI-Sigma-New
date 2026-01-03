"""
Automatic Submission Logger
Saves all user submissions with timestamps for data recovery and analysis
"""

import json
import os
from datetime import datetime
from typing import Dict, Any
from pathlib import Path


class SubmissionLogger:
    """Logs all user submissions to persistent storage"""
    
    def __init__(self, log_dir: str = "submissions"):
        self.log_dir = Path(log_dir)
        self.log_dir.mkdir(exist_ok=True)
        self.index_file = self.log_dir / "submission_index.json"
        self._load_index()
    
    def _load_index(self):
        """Load or create submission index"""
        if self.index_file.exists():
            with open(self.index_file, 'r') as f:
                self.index = json.load(f)
        else:
            self.index = {
                'total_submissions': 0,
                'submissions': []
            }
    
    def _save_index(self):
        """Save submission index"""
        with open(self.index_file, 'w') as f:
            json.dump(self.index, f, indent=2)
    
    def log_submission(
        self,
        content: str,
        input_method: str,
        metadata: Dict[str, Any] = None
    ) -> str:
        """
        Log a user submission
        
        Args:
            content: The submitted content
            input_method: How it was submitted (file, text, URL)
            metadata: Additional metadata (filename, URL, etc.)
            
        Returns:
            submission_id: Unique ID for this submission
        """
        timestamp = datetime.now()
        submission_id = timestamp.strftime("%Y%m%d_%H%M%S")
        
        submission_data = {
            'submission_id': submission_id,
            'timestamp': timestamp.isoformat(),
            'input_method': input_method,
            'content_length': len(content),
            'metadata': metadata or {}
        }
        
        # Save content to separate file
        content_file = self.log_dir / f"submission_{submission_id}.txt"
        with open(content_file, 'w') as f:
            f.write(f"=== SUBMISSION {submission_id} ===\n")
            f.write(f"Timestamp: {timestamp.isoformat()}\n")
            f.write(f"Input Method: {input_method}\n")
            f.write(f"Metadata: {json.dumps(metadata, indent=2)}\n")
            f.write(f"\n{'='*80}\n")
            f.write(f"CONTENT:\n")
            f.write(f"{'='*80}\n\n")
            f.write(content)
        
        # Save metadata to separate JSON
        meta_file = self.log_dir / f"submission_{submission_id}_meta.json"
        with open(meta_file, 'w') as f:
            json.dump(submission_data, f, indent=2)
        
        # Update index
        self.index['submissions'].append(submission_data)
        self.index['total_submissions'] += 1
        self._save_index()
        
        return submission_id
    
    def log_analysis_results(
        self,
        submission_id: str,
        results: Dict[str, Any]
    ):
        """Log analysis results for a submission"""
        results_file = self.log_dir / f"submission_{submission_id}_results.json"
        with open(results_file, 'w') as f:
            json.dump(results, f, indent=2, default=str)
    
    def get_recent_submissions(self, n: int = 10):
        """Get N most recent submissions"""
        return sorted(
            self.index['submissions'],
            key=lambda x: x['timestamp'],
            reverse=True
        )[:n]
    
    def get_submission_content(self, submission_id: str) -> str:
        """Retrieve content from a submission"""
        content_file = self.log_dir / f"submission_{submission_id}.txt"
        if content_file.exists():
            with open(content_file, 'r') as f:
                # Skip header, return just content
                lines = f.readlines()
                # Find content start
                for i, line in enumerate(lines):
                    if "CONTENT:" in line:
                        return ''.join(lines[i+2:])
        return None
    
    def search_submissions(self, keyword: str):
        """Search submissions by keyword"""
        matches = []
        for submission in self.index['submissions']:
            sid = submission['submission_id']
            content = self.get_submission_content(sid)
            if content and keyword.lower() in content.lower():
                matches.append({
                    **submission,
                    'preview': content[:200] + '...'
                })
        return matches
