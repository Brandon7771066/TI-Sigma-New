"""
ChatGPT Data Extractor - Streaming approach with SQLite storage
Handles 171MB HTML with 58,989 conversations efficiently
"""

import json
import re
import sqlite3
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Iterator
from html.parser import HTMLParser
import sys

class JSONExtractor(HTMLParser):
    """Stream HTML and extract JavaScript JSON segments"""
    
    def __init__(self):
        super().__init__()
        self.in_script = False
        self.script_content = []
    
    def handle_starttag(self, tag, attrs):
        if tag == 'script':
            self.in_script = True
    
    def handle_endtag(self, tag):
        if tag == 'script':
            self.in_script = False
    
    def handle_data(self, data):
        if self.in_script:
            self.script_content.append(data)
    
    def get_json_data(self):
        """Extract jsonData and assetsJson from script content"""
        full_script = ''.join(self.script_content)
        
        # Extract jsonData
        json_match = re.search(r'var jsonData = (\[.*?\]);', full_script, re.DOTALL)
        conversations = []
        if json_match:
            try:
                conversations = json.loads(json_match.group(1))
            except json.JSONDecodeError as e:
                print(f"Warning: JSON decode error: {e}")
        
        # Extract assetsJson
        assets_match = re.search(r'var assetsJson = (\{.*?\});', full_script, re.DOTALL)
        assets = {}
        if assets_match:
            try:
                assets = json.loads(assets_match.group(1))
            except:
                pass
        
        return conversations, assets

def init_database(db_path: str = 'chatgpt_data.db'):
    """Initialize SQLite database with schema"""
    
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    # Conversations table
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS conversations (
            id TEXT PRIMARY KEY,
            title TEXT,
            create_time REAL,
            update_time REAL,
            message_count INTEGER,
            categories TEXT,
            earliest_msg_time REAL,
            latest_msg_time REAL,
            user_msg_count INTEGER,
            assistant_msg_count INTEGER
        )
    ''')
    
    # Messages table
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS messages (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            conversation_id TEXT,
            author TEXT,
            content TEXT,
            timestamp REAL,
            msg_index INTEGER,
            FOREIGN KEY (conversation_id) REFERENCES conversations(id)
        )
    ''')
    
    # Create indexes
    cursor.execute('CREATE INDEX IF NOT EXISTS idx_conv_create_time ON conversations(create_time)')
    cursor.execute('CREATE INDEX IF NOT EXISTS idx_conv_categories ON conversations(categories)')
    cursor.execute('CREATE INDEX IF NOT EXISTS idx_msg_conv_id ON messages(conversation_id)')
    cursor.execute('CREATE INDEX IF NOT EXISTS idx_msg_timestamp ON messages(timestamp)')
    
    # Metadata table for tracking extraction
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS extraction_metadata (
            key TEXT PRIMARY KEY,
            value TEXT
        )
    ''')
    
    conn.commit()
    return conn

def parse_conversation(conv: Dict, conv_index: int) -> tuple[Dict[str, Any], List[Dict[str, Any]]]:
    """Parse single conversation into structured format"""
    
    # Generate unique ID
    conv_id = f"conv_{conv_index}_{conv.get('create_time', 0)}"
    
    messages = []
    current_node = conv.get('current_node')
    mapping = conv.get('mapping', {})
    
    # Traverse conversation tree
    msg_index = 0
    while current_node:
        node = mapping.get(current_node)
        if not node:
            break
            
        msg = node.get('message')
        if msg and msg.get('content') and msg['content'].get('parts'):
            author = msg['author']['role']
            if author in ['assistant', 'tool']:
                author = 'ChatGPT'
            elif author == 'system' and msg.get('metadata', {}).get('is_user_system_message'):
                author = 'Custom user info'
            
            content_parts = []
            for part in msg['content']['parts']:
                if isinstance(part, str) and part.strip():
                    content_parts.append(part)
            
            if content_parts:
                messages.append({
                    'conversation_id': conv_id,
                    'author': author,
                    'content': '\n'.join(content_parts),
                    'timestamp': msg.get('create_time', 0),
                    'msg_index': msg_index
                })
                msg_index += 1
        
        current_node = node.get('parent')
    
    messages.reverse()
    
    # Calculate statistics
    user_count = sum(1 for m in messages if m['author'] == 'user')
    assistant_count = sum(1 for m in messages if m['author'] == 'ChatGPT')
    timestamps = [m['timestamp'] for m in messages if m['timestamp']]
    
    conv_data = {
        'id': conv_id,
        'title': conv.get('title', 'Untitled'),
        'create_time': conv.get('create_time', 0),
        'update_time': conv.get('update_time', 0),
        'message_count': len(messages),
        'user_msg_count': user_count,
        'assistant_msg_count': assistant_count,
        'earliest_msg_time': min(timestamps) if timestamps else 0,
        'latest_msg_time': max(timestamps) if timestamps else 0
    }
    
    return conv_data, messages

def categorize_conversation(title: str, messages: List[Dict]) -> List[str]:
    """Categorize conversation by themes"""
    
    title_lower = title.lower()
    
    # Build search text from title + first few messages
    search_text = title_lower
    for msg in messages[:5]:
        search_text += ' ' + msg['content'][:500].lower()
    
    categories = []
    
    # TI Framework
    ti_keywords = ['gile', 'tralse', 'myrion', 'cosmic consciousness', 'grand myrion', 
                   'ti framework', 'transcendent intelligence', 'psi', 'i-cell', 'cc ',
                   'truth beauty', 'brandon storm']
    if any(kw in search_text for kw in ti_keywords):
        categories.append('TI Framework')
    
    # Philosophy
    phil_keywords = ['ontology', 'epistemology', 'metaphysics', 'consciousness', 
                     'truth', 'philosophy', 'logic', 'being', 'existence']
    if any(kw in search_text for kw in phil_keywords):
        categories.append('Philosophy')
    
    # Personal Life
    personal_keywords = ['ketamine', 'manic', 'bipolar', 'therapy', 'mental health',
                        'family', 'emily', 'mom', 'dad', 'friend', 'personal']
    if any(kw in search_text for kw in personal_keywords):
        categories.append('Personal Life')
    
    # Neuroscience/Bio
    neuro_keywords = ['eeg', 'fnirs', 'muse', 'mendi', 'brain', 'neural', 'neuron',
                     'hrv', 'biometric', 'polar', 'oura']
    if any(kw in search_text for kw in neuro_keywords):
        categories.append('Neuroscience')
    
    # Finance/Stock Market
    finance_keywords = ['stock', 'market', 'trading', 'prediction', 'god machine',
                       'alpha vantage', 'portfolio', 'investment', 'finance']
    if any(kw in search_text for kw in finance_keywords):
        categories.append('Finance')
    
    # Career/Monetization
    career_keywords = ['monetization', 'revenue', 'business', 'startup', 'career',
                      'job', 'work', 'employment', 'money']
    if any(kw in search_text for kw in career_keywords):
        categories.append('Career')
    
    # Relationships/Dating
    relationship_keywords = ['dating', 'romantic', 'partner', 'love', 'compatibility',
                            'attraction', 'relationship', 'girlfriend', 'boyfriend']
    if any(kw in search_text for kw in relationship_keywords):
        categories.append('Relationships')
    
    # Technical/Coding
    tech_keywords = ['python', 'code', 'streamlit', 'database', 'api', 'programming',
                    'debug', 'error', 'function', 'script']
    if any(kw in search_text for kw in tech_keywords):
        categories.append('Technical')
    
    if not categories:
        categories.append('General')
    
    return categories

def process_conversations_batch(conversations: List[Dict], conn: sqlite3.Connection, 
                                start_index: int = 0, batch_size: int = 1000):
    """Process conversations in batches and insert into database"""
    
    cursor = conn.cursor()
    total = len(conversations)
    
    for i in range(0, total, batch_size):
        batch = conversations[i:i+batch_size]
        batch_num = i // batch_size + 1
        total_batches = (total + batch_size - 1) // batch_size
        
        print(f"Processing batch {batch_num}/{total_batches} ({len(batch)} conversations)...")
        
        for j, conv_raw in enumerate(batch):
            conv_index = start_index + i + j
            
            try:
                conv_data, messages = parse_conversation(conv_raw, conv_index)
                
                # Categorize
                categories = categorize_conversation(conv_data['title'], messages)
                conv_data['categories'] = '|'.join(categories)
                
                # Insert conversation
                cursor.execute('''
                    INSERT OR REPLACE INTO conversations 
                    (id, title, create_time, update_time, message_count, categories,
                     earliest_msg_time, latest_msg_time, user_msg_count, assistant_msg_count)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ''', (
                    conv_data['id'], conv_data['title'], conv_data['create_time'],
                    conv_data['update_time'], conv_data['message_count'], conv_data['categories'],
                    conv_data['earliest_msg_time'], conv_data['latest_msg_time'],
                    conv_data['user_msg_count'], conv_data['assistant_msg_count']
                ))
                
                # Insert messages
                for msg in messages:
                    cursor.execute('''
                        INSERT INTO messages (conversation_id, author, content, timestamp, msg_index)
                        VALUES (?, ?, ?, ?, ?)
                    ''', (msg['conversation_id'], msg['author'], msg['content'], 
                          msg['timestamp'], msg['msg_index']))
                
            except Exception as e:
                print(f"Error processing conversation {conv_index}: {e}")
                continue
        
        conn.commit()
        print(f"✓ Batch {batch_num} committed to database")

def extract_and_store(html_path: str, db_path: str = 'chatgpt_data.db'):
    """Main extraction function"""
    
    print(f"Extracting JSON from {html_path}...")
    
    # Parse HTML to extract JSON
    parser = JSONExtractor()
    with open(html_path, 'r', encoding='utf-8') as f:
        parser.feed(f.read())
    
    conversations, assets = parser.get_json_data()
    print(f"✓ Extracted {len(conversations)} conversations")
    
    # Initialize database
    print("Initializing SQLite database...")
    conn = init_database(db_path)
    
    # Store metadata
    cursor = conn.cursor()
    cursor.execute('INSERT OR REPLACE INTO extraction_metadata VALUES (?, ?)',
                   ('extraction_date', datetime.now().isoformat()))
    cursor.execute('INSERT OR REPLACE INTO extraction_metadata VALUES (?, ?)',
                   ('source_file', html_path))
    cursor.execute('INSERT OR REPLACE INTO extraction_metadata VALUES (?, ?)',
                   ('total_conversations', str(len(conversations))))
    conn.commit()
    
    # Process in batches
    print("Processing conversations...")
    process_conversations_batch(conversations, conn, batch_size=1000)
    
    # Generate summary statistics
    cursor.execute('SELECT COUNT(*) FROM conversations')
    total_convs = cursor.fetchone()[0]
    
    cursor.execute('SELECT COUNT(*) FROM messages')
    total_msgs = cursor.fetchone()[0]
    
    cursor.execute('SELECT MIN(create_time), MAX(create_time) FROM conversations WHERE create_time > 0')
    date_range = cursor.fetchone()
    
    conn.close()
    
    print(f"\n{'='*60}")
    print(f"✅ EXTRACTION COMPLETE!")
    print(f"{'='*60}")
    print(f"Database: {db_path}")
    print(f"Conversations: {total_convs:,}")
    print(f"Messages: {total_msgs:,}")
    if date_range[0]:
        earliest = datetime.fromtimestamp(date_range[0])
        latest = datetime.fromtimestamp(date_range[1])
        print(f"Date Range: {earliest.date()} to {latest.date()} ({(latest-earliest).days} days)")
    print(f"{'='*60}\n")

if __name__ == '__main__':
    extract_and_store('attached_assets/chat_1763740519567.html')
