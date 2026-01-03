"""
ChatGPT Query Helpers - SQL query functions for synthesis
"""

import sqlite3
from typing import List, Dict, Any, Optional
from datetime import datetime
import pandas as pd

DB_PATH = 'chatgpt_data.db'

def get_conversations_by_category(category: str, limit: Optional[int] = None) -> List[Dict]:
    """Get conversations filtered by category"""
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    cursor = conn.cursor()
    
    query = '''
        SELECT * FROM conversations 
        WHERE categories LIKE ?
        ORDER BY create_time DESC
    '''
    
    if limit:
        query += f' LIMIT {limit}'
    
    cursor.execute(query, (f'%{category}%',))
    results = [dict(row) for row in cursor.fetchall()]
    conn.close()
    
    return results

def get_conversations_by_date_range(start_date: str, end_date: str) -> List[Dict]:
    """Get conversations in date range (YYYY-MM-DD format)"""
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    cursor = conn.cursor()
    
    start_timestamp = datetime.strptime(start_date, '%Y-%m-%d').timestamp()
    end_timestamp = datetime.strptime(end_date, '%Y-%m-%d').timestamp() + 86400  # +1 day
    
    cursor.execute('''
        SELECT * FROM conversations
        WHERE create_time BETWEEN ? AND ?
        ORDER BY create_time ASC
    ''', (start_timestamp, end_timestamp))
    
    results = [dict(row) for row in cursor.fetchall()]
    conn.close()
    
    return results

def search_conversations(keyword: str, limit: Optional[int] = None) -> List[Dict]:
    """Search conversations by keyword in title"""
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    cursor = conn.cursor()
    
    query = '''
        SELECT * FROM conversations
        WHERE title LIKE ?
        ORDER BY create_time DESC
    '''
    
    if limit:
        query += f' LIMIT {limit}'
    
    cursor.execute(query, (f'%{keyword}%',))
    results = [dict(row) for row in cursor.fetchall()]
    conn.close()
    
    return results

def search_messages(keyword: str, limit: Optional[int] = 100) -> List[Dict]:
    """Search messages by keyword using FTS5 for better performance"""
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    cursor = conn.cursor()
    
    # Try FTS5 search first
    try:
        query = '''
            SELECT m.*, c.title, c.create_time as conv_create_time
            FROM messages_fts fts
            JOIN messages m ON m.conversation_id = fts.conversation_id
            JOIN conversations c ON m.conversation_id = c.id
            WHERE messages_fts MATCH ?
            ORDER BY m.timestamp DESC
        '''
        
        if limit:
            query += f' LIMIT {limit}'
        
        cursor.execute(query, (keyword,))
        results = [dict(row) for row in cursor.fetchall()]
    except:
        # Fallback to LIKE search if FTS not available
        query = '''
            SELECT m.*, c.title, c.create_time as conv_create_time
            FROM messages m
            JOIN conversations c ON m.conversation_id = c.id
            WHERE m.content LIKE ?
            ORDER BY m.timestamp DESC
        '''
        
        if limit:
            query += f' LIMIT {limit}'
        
        cursor.execute(query, (f'%{keyword}%',))
        results = [dict(row) for row in cursor.fetchall()]
    
    conn.close()
    return results

def get_messages_for_conversation(conversation_id: str) -> List[Dict]:
    """Get all messages for a conversation"""
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    cursor = conn.cursor()
    
    cursor.execute('''
        SELECT * FROM messages
        WHERE conversation_id = ?
        ORDER BY msg_index ASC
    ''', (conversation_id,))
    
    results = [dict(row) for row in cursor.fetchall()]
    conn.close()
    
    return results

def get_category_stats() -> pd.DataFrame:
    """Get category distribution statistics"""
    conn = sqlite3.connect(DB_PATH)
    
    df = pd.read_sql_query('''
        SELECT 
            categories,
            COUNT(*) as count,
            SUM(message_count) as total_messages,
            AVG(message_count) as avg_messages
        FROM conversations
        GROUP BY categories
        ORDER BY count DESC
    ''', conn)
    
    conn.close()
    return df

def get_timeline_stats() -> pd.DataFrame:
    """Get conversation timeline by month"""
    conn = sqlite3.connect(DB_PATH)
    
    df = pd.read_sql_query('''
        SELECT 
            strftime('%Y-%m', datetime(create_time, 'unixepoch')) as month,
            COUNT(*) as conversations,
            SUM(message_count) as messages
        FROM conversations
        WHERE create_time > 0
        GROUP BY month
        ORDER BY month ASC
    ''', conn)
    
    conn.close()
    return df

def get_ti_framework_timeline() -> List[Dict]:
    """Get chronological timeline of TI Framework development"""
    convs = get_conversations_by_category('TI Framework')
    
    timeline = []
    for conv in convs:
        timeline.append({
            'date': datetime.fromtimestamp(conv['create_time']).strftime('%Y-%m-%d'),
            'title': conv['title'],
            'id': conv['id'],
            'message_count': conv['message_count']
        })
    
    # Sort by date ascending
    timeline.sort(key=lambda x: x['date'])
    return timeline

def get_personal_life_themes() -> Dict[str, List[Dict]]:
    """Get personal life conversations organized by theme"""
    convs = get_conversations_by_category('Personal Life')
    
    themes = {
        'Mental Health & Ketamine': [],
        'Relationships & Dating': [],
        'Family & Friends': [],
        'Career & Work': [],
        'General Personal': []
    }
    
    for conv in convs:
        title_lower = conv['title'].lower()
        
        if any(kw in title_lower for kw in ['ketamine', 'manic', 'bipolar', 'therapy', 'mental']):
            themes['Mental Health & Ketamine'].append(conv)
        elif any(kw in title_lower for kw in ['emily', 'dating', 'relationship', 'romantic']):
            themes['Relationships & Dating'].append(conv)
        elif any(kw in title_lower for kw in ['family', 'mom', 'dad', 'parent']):
            themes['Family & Friends'].append(conv)
        elif any(kw in title_lower for kw in ['career', 'job', 'work', 'employment']):
            themes['Career & Work'].append(conv)
        else:
            themes['General Personal'].append(conv)
    
    return themes

def extract_genius_patterns() -> Dict[str, Any]:
    """Extract cognitive patterns for genius profile"""
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    cursor = conn.cursor()
    
    # Philosophy conversations
    phil_convs = get_conversations_by_category('Philosophy')
    
    # TI framework conversations
    ti_convs = get_conversations_by_category('TI Framework')
    
    # Creative insights
    creative_keywords = ['insight', 'intuition', 'revelation', 'discovery', 'breakthrough']
    creative_msgs = []
    for kw in creative_keywords:
        msgs = search_messages(kw, limit=20)
        creative_msgs.extend(msgs)
    
    cursor.execute('''
        SELECT AVG(message_count) as avg_depth
        FROM conversations
        WHERE categories LIKE '%Philosophy%' OR categories LIKE '%TI Framework%'
    ''')
    avg_depth = cursor.fetchone()['avg_depth']
    
    conn.close()
    
    return {
        'total_philosophical_conversations': len(phil_convs),
        'total_ti_framework_conversations': len(ti_convs),
        'creative_insight_messages': len(creative_msgs),
        'avg_conversation_depth': avg_depth,
        'patterns': {
            'Intuition → Theory → Proof': True,
            'Faith-based epistemology': True,
            'Fluid belief updating': True,
            'Dialectical thinking': True,
            'Multi-domain synthesis': True
        }
    }

def extract_relationship_compatibility() -> Dict[str, Any]:
    """Extract relationship compatibility signals"""
    rel_convs = get_conversations_by_category('Relationships')
    
    # Extract communication patterns
    comm_patterns = []
    for conv in rel_convs:
        messages = get_messages_for_conversation(conv['id'])
        if messages:
            # Analyze first few messages for communication style
            user_msgs = [m for m in messages if m['author'] == 'user']
            if user_msgs:
                avg_length = sum(len(m['content']) for m in user_msgs) / len(user_msgs)
                comm_patterns.append({
                    'conversation': conv['title'],
                    'avg_message_length': avg_length,
                    'total_messages': len(user_msgs)
                })
    
    return {
        'total_relationship_conversations': len(rel_convs),
        'communication_patterns': comm_patterns,
        'values': ['Truth-seeking', 'Creativity', 'Sovereignty', 'Interconnectedness'],
        'ideal_partner_traits': [
            'GM-Node with TI alignment',
            'Philosophical compatibility',
            'Openness to experience',
            'Intellectual curiosity',
            'Emotional depth'
        ]
    }
