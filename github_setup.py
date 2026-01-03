"""
GitHub Repository Setup for TI Framework Project
Uses Replit's GitHub connection to create and configure repository
"""

import os
import requests
from github import Github

def get_github_access_token():
    """Get GitHub access token from Replit connection"""
    hostname = os.environ.get('REPLIT_CONNECTORS_HOSTNAME')
    
    repl_identity = os.environ.get('REPL_IDENTITY')
    web_repl_renewal = os.environ.get('WEB_REPL_RENEWAL')
    
    if repl_identity:
        x_replit_token = f'repl {repl_identity}'
    elif web_repl_renewal:
        x_replit_token = f'depl {web_repl_renewal}'
    else:
        raise Exception('X_REPLIT_TOKEN not found')
    
    response = requests.get(
        f'https://{hostname}/api/v2/connection?include_secrets=true&connector_names=github',
        headers={
            'Accept': 'application/json',
            'X_REPLIT_TOKEN': x_replit_token
        }
    )
    
    data = response.json()
    connection = data.get('items', [{}])[0]
    settings = connection.get('settings', {})
    
    access_token = settings.get('access_token') or settings.get('oauth', {}).get('credentials', {}).get('access_token')
    
    if not access_token:
        raise Exception('GitHub not connected or access token not found')
    
    return access_token

def get_github_client():
    """Get authenticated GitHub client"""
    token = get_github_access_token()
    return Github(token)

def get_user_info():
    """Get info about the authenticated GitHub user"""
    g = get_github_client()
    user = g.get_user()
    return {
        'login': user.login,
        'name': user.name,
        'email': user.email,
        'repos_url': user.repos_url,
        'public_repos': user.public_repos
    }

def list_user_repos():
    """List user's repositories"""
    g = get_github_client()
    user = g.get_user()
    repos = []
    for repo in user.get_repos():
        repos.append({
            'name': repo.name,
            'full_name': repo.full_name,
            'private': repo.private,
            'url': repo.html_url
        })
    return repos

def create_repository(name, description, private=False):
    """Create a new GitHub repository"""
    g = get_github_client()
    user = g.get_user()
    
    try:
        repo = user.create_repo(  # type: ignore[union-attr]
            name=name,
            description=description,
            private=private,
            auto_init=False
        )
        return {
            'success': True,
            'name': repo.name,
            'full_name': repo.full_name,
            'url': repo.html_url,
            'clone_url': repo.clone_url,
            'ssh_url': repo.ssh_url
        }
    except Exception as e:
        return {
            'success': False,
            'error': str(e)
        }

if __name__ == "__main__":
    print("=" * 60)
    print("GitHub Connection Status")
    print("=" * 60)
    
    try:
        user_info = get_user_info()
        print(f"\n✅ Connected as: {user_info['login']}")
        print(f"   Name: {user_info.get('name', 'N/A')}")
        print(f"   Public repos: {user_info['public_repos']}")
        
        print("\n📂 Your repositories:")
        repos = list_user_repos()
        for repo in repos[:10]:
            visibility = "🔒" if repo['private'] else "🌐"
            print(f"   {visibility} {repo['name']}")
        
        if len(repos) > 10:
            print(f"   ... and {len(repos) - 10} more")
            
    except Exception as e:
        print(f"\n❌ Error: {e}")
