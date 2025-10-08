# TCDB Core Authentication System

## Overview

TCDB Core now includes a complete authentication system with:
- ✅ **Homepage** - Beautiful landing page explaining TCDB features
- ✅ **User Authentication** - Simple email/password signup and login
- ✅ **Dashboard** - User dashboard showing API keys
- ✅ **API Key Management** - Create, view, and revoke API keys
- ✅ **Secure Authentication** - JWT tokens for sessions, bcrypt for passwords
- ✅ **Database** - SQLite database for users and API keys

## Quick Start

### 1. Install Dependencies

```bash
pip install sqlalchemy passlib[bcrypt] python-jose[cryptography] python-multipart jinja2 email-validator
```

Or install from pyproject.toml:

```bash
pip install -e .
```

### 2. Run the Server

```bash
cd python
python -m uvicorn tcdb_api.app:app --reload --port 8000
```

### 3. Access the Application

- **Homepage**: http://localhost:8000
- **Login**: http://localhost:8000/auth/login
- **Signup**: http://localhost:8000/auth/signup
- **Dashboard**: http://localhost:8000/dashboard
- **API Docs**: http://localhost:8000/docs

## Features

### Homepage

The homepage (`/`) provides:
- Overview of TCDB Core features
- Quick start code examples
- Links to signup and API documentation
- Responsive design with modern UI

### User Authentication

#### Signup
- **Endpoint**: `POST /auth/signup`
- **Form**: Email + Password (minimum 8 characters)
- **Creates**: New user account in database
- **Redirects**: To login page after successful signup

#### Login
- **Endpoint**: `POST /auth/login`
- **Form**: Email + Password
- **Creates**: Session cookie with JWT token (7 days expiry)
- **Redirects**: To dashboard after successful login

#### Logout
- **Endpoint**: `POST /auth/logout`
- **Action**: Clears session cookie

### Dashboard

The dashboard (`/dashboard`) shows:
- User email
- List of API keys with:
  - Key name
  - Key preview (first 12 characters)
  - Creation date
  - Last used date
  - Active/inactive status
- Create new API key button
- Quick start code examples

### API Key Management

#### Create API Key
- **Endpoint**: `POST /keys/`
- **Request**: `{"name": "My API Key"}`
- **Response**: Full API key (shown only once!)
- **Format**: `tcdb_<64 hex characters>`

#### List API Keys
- **Endpoint**: `GET /keys/`
- **Response**: List of user's API keys (with preview only)

#### Revoke API Key
- **Endpoint**: `DELETE /keys/{key_id}`
- **Action**: Deactivates the API key

#### Activate API Key
- **Endpoint**: `POST /keys/{key_id}/activate`
- **Action**: Reactivates a revoked API key

## Using API Keys

### With cURL

```bash
curl -X POST http://localhost:8000/pipeline/run \
  -H "X-API-Key: tcdb_your_api_key_here" \
  -H "Content-Type: application/json" \
  -d '{
    "data": [[0, 0], [1, 0], [0, 1], [1, 1]],
    "max_dimension": 2
  }'
```

### With Python

```python
import requests

response = requests.post(
    "http://localhost:8000/pipeline/run",
    headers={"X-API-Key": "tcdb_your_api_key_here"},
    json={
        "data": [[0, 0], [1, 0], [0, 1], [1, 1]],
        "max_dimension": 2
    }
)

print(response.json())
```

### With JavaScript

```javascript
fetch('http://localhost:8000/pipeline/run', {
  method: 'POST',
  headers: {
    'X-API-Key': 'tcdb_your_api_key_here',
    'Content-Type': 'application/json'
  },
  body: JSON.stringify({
    data: [[0, 0], [1, 0], [0, 1], [1, 1]],
    max_dimension: 2
  })
})
.then(res => res.json())
.then(data => console.log(data));
```

## Database Schema

### Users Table

```sql
CREATE TABLE users (
    id INTEGER PRIMARY KEY,
    email VARCHAR UNIQUE NOT NULL,
    hashed_password VARCHAR NOT NULL,
    is_active BOOLEAN DEFAULT TRUE,
    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
);
```

### API Keys Table

```sql
CREATE TABLE api_keys (
    id INTEGER PRIMARY KEY,
    key VARCHAR UNIQUE NOT NULL,
    name VARCHAR NOT NULL,
    user_id INTEGER NOT NULL,
    is_active BOOLEAN DEFAULT TRUE,
    created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
    last_used_at DATETIME,
    FOREIGN KEY (user_id) REFERENCES users(id)
);
```

## Security Features

### Password Security
- **Hashing**: bcrypt with automatic salt generation
- **Minimum Length**: 8 characters
- **Storage**: Only hashed passwords stored in database

### Session Security
- **JWT Tokens**: Signed with secret key
- **Expiry**: 7 days
- **HttpOnly Cookies**: Prevents XSS attacks
- **SameSite**: Lax (prevents CSRF)

### API Key Security
- **Format**: `tcdb_<64 random hex characters>`
- **Generation**: Cryptographically secure random
- **Storage**: Plain text in database (for verification)
- **Revocation**: Can be deactivated without deletion
- **Last Used Tracking**: Monitors API key usage

## Configuration

### Environment Variables

```bash
# Secret key for JWT tokens (CHANGE IN PRODUCTION!)
SECRET_KEY=your-secret-key-here

# Database URL (defaults to SQLite)
DATABASE_URL=sqlite:///./tcdb.db

# Or use PostgreSQL
DATABASE_URL=postgresql://user:password@localhost/tcdb
```

### Production Deployment

For production, make sure to:

1. **Change SECRET_KEY**: Use a strong random key
   ```bash
   python -c "import secrets; print(secrets.token_hex(32))"
   ```

2. **Use PostgreSQL**: Instead of SQLite
   ```bash
   DATABASE_URL=postgresql://user:password@host/database
   ```

3. **Enable HTTPS**: Use SSL/TLS certificates

4. **Configure CORS**: Restrict allowed origins in `app.py`

5. **Set up rate limiting**: Already configured with SlowAPI

## API Endpoints

### Public Endpoints (No Auth Required)

- `GET /` - Homepage
- `GET /auth/login` - Login page
- `GET /auth/signup` - Signup page
- `POST /auth/signup` - Create account
- `POST /auth/login` - Login
- `GET /docs` - API documentation
- `GET /health` - Health check

### Protected Endpoints (Require Login)

- `GET /dashboard` - User dashboard
- `GET /keys/` - List API keys
- `POST /keys/` - Create API key
- `DELETE /keys/{key_id}` - Revoke API key
- `POST /keys/{key_id}/activate` - Activate API key

### API Endpoints (Require API Key)

To protect API endpoints with API keys, add the `verify_api_key` dependency:

```python
from fastapi import Depends
from tcdb_api.middleware import verify_api_key
from tcdb_api.database import User

@router.post("/protected-endpoint")
async def protected_endpoint(
    current_user: User = Depends(verify_api_key)
):
    # current_user contains the authenticated user
    return {"message": "Success", "user_email": current_user.email}
```

## File Structure

```
python/tcdb_api/
├── app.py                 # Main FastAPI application
├── auth.py                # Authentication utilities
├── database.py            # Database models and session
├── middleware.py          # API key verification middleware
├── models.py              # Pydantic models
├── routers/
│   ├── auth.py           # Auth endpoints (signup, login)
│   ├── keys.py           # API key management
│   ├── health.py         # Health check
│   ├── pipeline.py       # TDA pipeline
│   ├── tda.py            # TDA endpoints
│   ├── certificate.py    # Provenance certificates
│   ├── reasoner.py       # Constraint checking
│   └── eval.py           # LLM hallucination detection
├── templates/
│   ├── base.html         # Base template
│   ├── index.html        # Homepage
│   ├── login.html        # Login page
│   ├── signup.html       # Signup page
│   └── dashboard.html    # Dashboard
└── static/
    └── style.css         # Styles
```

## Testing

### Manual Testing

1. **Signup**: Go to http://localhost:8000/auth/signup
2. **Login**: Go to http://localhost:8000/auth/login
3. **Create API Key**: Go to http://localhost:8000/dashboard
4. **Test API**: Use the API key with any endpoint

### Automated Testing

```python
from fastapi.testclient import TestClient
from tcdb_api.app import app

client = TestClient(app)

# Test signup
response = client.post("/auth/api/signup", json={
    "email": "test@example.com",
    "password": "testpassword123"
})
assert response.status_code == 200

# Test login
response = client.post("/auth/api/login", json={
    "email": "test@example.com",
    "password": "testpassword123"
})
assert response.status_code == 200
token = response.json()["access_token"]
```

## Troubleshooting

### Database Issues

If you get database errors, delete the database and restart:

```bash
rm tcdb.db
python -m uvicorn tcdb_api.app:app --reload
```

### Import Errors

Make sure all dependencies are installed:

```bash
pip install -e .
```

### Static Files Not Found

Make sure you're running from the `python/` directory:

```bash
cd python
python -m uvicorn tcdb_api.app:app --reload
```

## Next Steps

- [ ] Add email verification
- [ ] Add password reset functionality
- [ ] Add OAuth providers (Google, GitHub)
- [ ] Add API usage analytics
- [ ] Add rate limiting per API key
- [ ] Add API key scopes/permissions
- [ ] Add team/organization support
- [ ] Add billing integration

## Support

For issues or questions, please open an issue on GitHub:
https://github.com/DeepFriedCyber/tcdb-core/issues

