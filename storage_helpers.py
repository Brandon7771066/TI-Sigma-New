"""
Storage Helper Functions for Replit Object Storage
Handles persistent file storage for large files, images, and ChatGPT exports.
"""

from replit.object_storage import Client
from typing import List, Dict, Optional, BinaryIO
import os
from datetime import datetime
import json

class StorageManager:
    """Manages file storage operations using Replit Object Storage."""
    
    def __init__(self, bucket_id=None):
        """Initialize storage manager with specific bucket (or default)."""
        try:
            # Create client with bucket_id (None = use default bucket)
            self.client = Client(bucket_id=bucket_id)
            self.bucket_id = bucket_id or "default"
            
            # Smoke test: verify bucket is accessible
            try:
                list(self.client.list())
                print(f"✅ Object storage connected to bucket: {self.bucket_id}")
            except Exception as e:
                print(f"⚠️ Bucket '{self.bucket_id}' initialization: {e}")
        except Exception as e:
            print(f"❌ Storage initialization failed: {e}")
            self.client = None
    
    def upload_file(self, file_data: BinaryIO, filename: str, folder: str = "") -> bool:
        """
        Upload a file to object storage with streaming for large files.
        
        Args:
            file_data: File binary data (from st.file_uploader)
            filename: Name of the file
            folder: Optional folder path (e.g., 'chatgpt_history/', 'graphs/')
            
        Returns:
            bool: True if successful, False otherwise
        """
        try:
            if not self.client:
                print("Storage client not initialized")
                return False
            
            # Construct full path
            if folder and not folder.endswith('/'):
                folder += '/'
            
            full_path = f"{folder}{filename}"
            
            # Get file size BEFORE reading
            file_size = 0
            if hasattr(file_data, 'size'):
                file_size = file_data.size
            elif hasattr(file_data, 'tell') and hasattr(file_data, 'seek'):
                # Get size by seeking to end
                current_pos = file_data.tell()
                file_data.seek(0, 2)  # Seek to end
                file_size = file_data.tell()
                file_data.seek(current_pos)  # Restore position
            
            # HARD LIMIT: Block uploads > 200MB to prevent OOM
            MAX_SIZE_MB = 200
            MAX_SIZE_BYTES = MAX_SIZE_MB * 1024 * 1024
            
            if file_size > MAX_SIZE_BYTES:
                size_mb = file_size / (1024 * 1024)
                print(f"❌ File too large: {size_mb:.1f} MB (limit: {MAX_SIZE_MB} MB)")
                raise ValueError(
                    f"File size ({size_mb:.1f} MB) exceeds {MAX_SIZE_MB} MB limit. "
                    f"Please split your ChatGPT export into smaller date ranges."
                )
            
            # Upload file (reads entire file into memory - unavoidable with current SDK)
            if file_size > 50 * 1024 * 1024:  # Warn for files > 50MB
                print(f"⚠️ Uploading large file: {file_size / (1024*1024):.1f} MB...")
            
            data = file_data.read()
            self.client.upload_from_bytes(full_path, data)
            
            # Store metadata
            metadata = {
                'filename': filename,
                'folder': folder,
                'uploaded_at': datetime.now().isoformat(),
                'size': file_size
            }
            self.client.upload_from_text(f"{full_path}.metadata", json.dumps(metadata))
            
            print(f"✅ Uploaded {filename} ({file_size / (1024*1024):.1f} MB)")
            return True
            
        except Exception as e:
            print(f"❌ Upload error: {e}")
            return False
    
    def download_file(self, filepath: str) -> Optional[bytes]:
        """
        Download a file from object storage.
        
        Args:
            filepath: Full path to file in storage
            
        Returns:
            bytes: File content, or None if not found
        """
        try:
            return self.client.download_as_bytes(filepath)
        except Exception as e:
            print(f"Download error: {e}")
            return None
    
    def list_files(self, folder: str = "") -> List[str]:
        """
        List all files in a folder.
        
        Args:
            folder: Folder path (e.g., 'chatgpt_history/')
            
        Returns:
            List of file paths
        """
        try:
            # Convert to list of strings
            all_files = [str(f) for f in self.client.list()]
            
            # Filter by folder if specified
            if folder:
                if not folder.endswith('/'):
                    folder += '/'
                files = [f for f in all_files if f.startswith(folder) and not f.endswith('.metadata')]
            else:
                files = [f for f in all_files if not f.endswith('.metadata')]
            
            return sorted(files)
        except Exception as e:
            print(f"List error: {e}")
            return []
    
    def delete_file(self, filepath: str) -> bool:
        """
        Delete a file from storage.
        
        Args:
            filepath: Full path to file
            
        Returns:
            bool: True if successful
        """
        try:
            self.client.delete(filepath)
            # Also delete metadata if exists
            try:
                self.client.delete(f"{filepath}.metadata")
            except:
                pass
            return True
        except Exception as e:
            print(f"Delete error: {e}")
            return False
    
    def get_metadata(self, filepath: str) -> Optional[Dict]:
        """Get file metadata."""
        try:
            metadata_str = self.client.download_as_text(f"{filepath}.metadata")
            return json.loads(metadata_str)
        except:
            return None
    
    def save_text(self, filepath: str, content: str) -> bool:
        """Save text content to storage."""
        try:
            self.client.upload_from_text(filepath, content)
            return True
        except Exception as e:
            print(f"Save text error: {e}")
            return False
    
    def load_text(self, filepath: str) -> Optional[str]:
        """Load text content from storage."""
        try:
            return self.client.download_as_text(filepath)
        except Exception as e:
            print(f"Load text error: {e}")
            return None
    
    def create_folder_structure(self):
        """Create organized folder structure for different file types."""
        folders = [
            'chatgpt_history/raw/',
            'chatgpt_history/by_date/',
            'chatgpt_history/by_concept/',
            'graphs/',
            'images/',
            'exports/',
            'drafts/'
        ]
        
        # Create placeholder files to establish folder structure
        for folder in folders:
            try:
                self.client.upload_from_text(f"{folder}.placeholder", f"Folder: {folder}")
            except:
                pass
        
        return folders
