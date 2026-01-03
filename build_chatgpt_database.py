"""
Build ChatGPT Database - Standalone script for database construction
Extracts from attached_assets/chat_1763740519567.html or chatgpt_all_conversations.json
"""

import sqlite3
import json
from datetime import datetime
from pathlib import Path

def categorize(title: str, messages_preview: str) -> str:
    """Enhanced categorization with TI-specific keywords"""
    text = (title + ' ' + messages_preview).lower()
    
    categories = []
    
    # TI Framework - Enhanced keywords
    ti_keywords = [
        'gile', 'tralse', 'myrion', 'cosmic consciousness', 'grand myrion', 
        'ti framework', 'transcendent intelligence', 'psi', 'i-cell', 'cc ',
        'truth beauty', 'brandon storm', 'tralsebit', 'mono truth', 
        'ingenious truth', 'myrion resolution', 'gile optimization',
        'pre-tralse', 'double tralse', 'consciousness shell', 'nnl', 'prf theory'
    ]
    if any(kw in text for kw in ti_keywords):
        categories.append('TI Framework')
    
    # Philosophy
    phil_keywords = [
        'ontology', 'epistemology', 'metaphysics', 'consciousness', 
        'truth', 'philosophy', 'logic', 'being', 'existence', 'reality',
        'intuition', 'faith', 'revelation', 'dialectical'
    ]
    if any(kw in text for kw in phil_keywords):
        categories.append('Philosophy')
    
    # Personal Life - Enhanced
    personal_keywords = [
        'ketamine', 'manic', 'bipolar', 'therapy', 'mental health',
        'family', 'emily', 'mom', 'dad', 'friend', 'personal',
        'manic episode', 'depression', 'anxiety', 'emotional'
    ]
    if any(kw in text for kw in personal_keywords):
        categories.append('Personal Life')
    
    # Neuroscience/Bio
    neuro_keywords = [
        'eeg', 'fnirs', 'muse', 'mendi', 'brain', 'neural', 'neuron',
        'hrv', 'biometric', 'polar', 'oura', 'fmri', 'biophoton',
        'neuroscience', 'biofield', 'meridian', 'chakra'
    ]
    if any(kw in text for kw in neuro_keywords):
        categories.append('Neuroscience')
    
    # Finance/Stock Market
    finance_keywords = [
        'stock', 'market', 'trading', 'prediction', 'god machine',
        'alpha vantage', 'portfolio', 'investment', 'finance',
        'kalshi', 'metaculus', 'hedge fund'
    ]
    if any(kw in text for kw in finance_keywords):
        categories.append('Finance')
    
    # Career/Monetization
    career_keywords = [
        'monetization', 'revenue', 'business', 'startup', 'career',
        'job', 'work', 'employment', 'money', 'income', 'salary'
    ]
    if any(kw in text for kw in career_keywords):
        categories.append('Career')
    
    # Relationships/Dating
    relationship_keywords = [
        'dating', 'romantic', 'partner', 'love', 'compatibility',
        'attraction', 'relationship', 'girlfriend', 'boyfriend',
        'marriage', 'gottman', 'gm-node', 'ti-ally'
    ]
    if any(kw in text for kw in relationship_keywords):
        categories.append('Relationships')
    
    # Technical/Coding
    tech_keywords = [
        'python', 'code', 'streamlit', 'database', 'api', 'programming',
        'debug', 'error', 'function', 'script', 'javascript', 'typescript'
    ]
    if any(kw in text for kw in tech_keywords):
        categories.append('Technical')
    
    return '|'.join(categories) if categories else 'General'

def parse_conversation_full(conv: dict, conv_index: int) -> tuple:
    """
    Parse conversation extracting ALL messages from mapping tree
    Fixes: Previous version only followed parent chain, missing branches
    """
    
    conv_id = conv.get('id', f"conv_{conv_index}_{conv.get('create_time', 0)}")
    
    messages = []
    mapping = conv.get('mapping', {})
    
    # Traverse entire mapping to capture ALL messages
    visited = set()
    
    def extract_message(node_id, depth=0):
        if node_id in visited or node_id not in mapping:
            return
        
        visited.add(node_id)
        node = mapping[node_id]
        
        msg = node.get('message')
        if msg and msg.get('content') and msg['content'].get('parts'):
            author = msg['author']['role']
            if author in ['assistant', 'tool']:
                author = 'ChatGPT'
            elif author == 'system' and msg.get('metadata', {}).get('is_user_system_message'):
                author = 'Custom user info'
            
            parts = [p for p in msg['content']['parts'] if isinstance(p, str) and p.strip()]
            if parts:
                messages.append({
                    'conversation_id': conv_id,
                    'author': author,
                    'content': '\n'.join(parts),
                    'timestamp': msg.get('create_time', 0),
                    'node_id': node_id
                })
        
        # Traverse children
        for child_id in node.get('children', []):
            extract_message(child_id, depth + 1)
    
    # Start from root nodes (nodes with no parent)
    root_nodes = [nid for nid, node in mapping.items() if not node.get('parent')]
    for root in root_nodes:
        extract_message(root)
    
    # Sort messages by timestamp
    messages.sort(key=lambda m: m.get('timestamp', 0))
    
    # Add message indices
    for i, msg in enumerate(messages):
        msg['msg_index'] = i
    
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

def build_database():
    """Main database build function"""
    
    print("="*60)
    print("ChatGPT Database Builder")
    print("="*60)
    
    # Check for pre-extracted JSON
    json_path = Path('chatgpt_all_conversations.json')
    
    if not json_path.exists():
        print("ERROR: chatgpt_all_conversations.json not found!")
        print("Please run the extraction first or ensure the file exists.")
        return False
    
    # Load conversations
    print(f"Loading conversations from {json_path}...")
    with open(json_path, 'r', encoding='utf-8') as f:
        conversations = json.load(f)
    
    print(f"✓ Loaded {len(conversations):,} conversations")
    
    # Initialize database
    db_path = 'chatgpt_data.db'
    print(f"Initializing database: {db_path}")
    
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    # Drop existing tables for clean rebuild
    cursor.execute('DROP TABLE IF EXISTS messages')
    cursor.execute('DROP TABLE IF EXISTS conversations')
    
    # Create schema
    cursor.execute('''
        CREATE TABLE conversations (
            id TEXT PRIMARY KEY,
            title TEXT,
            create_time REAL,
            update_time REAL,
            message_count INTEGER,
            categories TEXT,
            user_msg_count INTEGER,
            assistant_msg_count INTEGER,
            earliest_msg_time REAL,
            latest_msg_time REAL
        )
    ''')
    
    cursor.execute('''
        CREATE TABLE messages (
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
    cursor.execute('CREATE INDEX idx_conv_create_time ON conversations(create_time)')
    cursor.execute('CREATE INDEX idx_conv_categories ON conversations(categories)')
    cursor.execute('CREATE INDEX idx_msg_conv_id ON messages(conversation_id)')
    cursor.execute('CREATE INDEX idx_msg_timestamp ON messages(timestamp)')
    
    # Add FTS5 for better search
    cursor.execute('''
        CREATE VIRTUAL TABLE IF NOT EXISTS messages_fts 
        USING fts5(content, conversation_id)
    ''')
    
    conn.commit()
    print("✓ Database schema created with FTS5 search")
    
    # Process conversations
    print(f"Processing {len(conversations)} conversations...")
    
    for i, conv_raw in enumerate(conversations):
        try:
            conv_data, messages = parse_conversation_full(conv_raw, i)
            
            # Categorize based on full message content
            preview = ' '.join([m['content'][:300] for m in messages[:5]])
            categories = categorize(conv_data['title'], preview)
            conv_data['categories'] = categories
            
            # Insert conversation
            cursor.execute('''
                INSERT INTO conversations 
                (id, title, create_time, update_time, message_count, categories,
                 user_msg_count, assistant_msg_count, earliest_msg_time, latest_msg_time)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (
                conv_data['id'], conv_data['title'], conv_data['create_time'],
                conv_data['update_time'], conv_data['message_count'], conv_data['categories'],
                conv_data['user_msg_count'], conv_data['assistant_msg_count'],
                conv_data['earliest_msg_time'], conv_data['latest_msg_time']
            ))
            
            # Insert messages
            for msg in messages:
                cursor.execute('''
                    INSERT INTO messages (conversation_id, author, content, timestamp, msg_index)
                    VALUES (?, ?, ?, ?, ?)
                ''', (msg['conversation_id'], msg['author'], msg['content'], 
                      msg['timestamp'], msg['msg_index']))
                
                # Insert into FTS
                cursor.execute('''
                    INSERT INTO messages_fts (content, conversation_id)
                    VALUES (?, ?)
                ''', (msg['content'], msg['conversation_id']))
            
            if (i + 1) % 100 == 0:
                print(f"  Processed {i+1}/{len(conversations)} conversations...")
                conn.commit()
        
        except Exception as e:
            print(f"ERROR processing conversation {i}: {e}")
            continue
    
    conn.commit()
    
    # Stats
    cursor.execute('SELECT COUNT(*) FROM conversations')
    total_convs = cursor.fetchone()[0]
    
    cursor.execute('SELECT COUNT(*) FROM messages')
    total_msgs = cursor.fetchone()[0]
    
    cursor.execute('SELECT MIN(create_time), MAX(create_time) FROM conversations WHERE create_time > 0')
    date_range = cursor.fetchone()
    
    cursor.execute('''
        SELECT categories, COUNT(*) as count 
        FROM conversations 
        GROUP BY categories 
        ORDER BY count DESC 
        LIMIT 10
    ''')
    category_stats = cursor.fetchall()
    
    conn.close()
    
    print(f"\n{'='*60}")
    print(f"✅ DATABASE BUILD COMPLETE!")
    print(f"{'='*60}")
    print(f"Database: {db_path}")
    print(f"Conversations: {total_convs:,}")
    print(f"Messages: {total_msgs:,}")
    
    if date_range[0]:
        earliest = datetime.fromtimestamp(date_range[0])
        latest = datetime.fromtimestamp(date_range[1])
        print(f"Date Range: {earliest.date()} to {latest.date()} ({(latest-earliest).days} days)")
    
    print(f"\nTop Categories:")
    for cat, count in category_stats:
        print(f"  {cat}: {count}")
    print(f"{'='*60}\n")
    
    return True

if __name__ == '__main__':
    success = build_database()
    exit(0 if success else 1)
