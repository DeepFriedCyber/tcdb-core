# Clerk Authentication Setup Guide

## Overview

This API uses [Clerk](https://clerk.com) for secure, production-ready authentication. No API keys are hardcoded - all credentials are managed through environment variables.

## Quick Start

### 1. Create a Clerk Account

1. Go to [https://clerk.com](https://clerk.com)
2. Sign up for a free account
3. Create a new application

### 2. Get Your Clerk Keys

In your Clerk Dashboard:

1. Go to **API Keys** section
2. Copy your **Publishable Key** (starts with `pk_test_` or `pk_live_`)
3. Copy your **Secret Key** (starts with `sk_test_` or `sk_live_`)

⚠️ **IMPORTANT**: Never commit your secret key to version control!

### 3. Configure Environment Variables

1. Copy the example environment file:
   ```bash
   cp .env.example .env
   ```

2. Edit `.env` and add your Clerk keys:
   ```bash
   CLERK_SECRET_KEY=sk_test_your_secret_key_here
   CLERK_PUBLISHABLE_KEY=pk_test_your_publishable_key_here
   FLASK_SECRET_KEY=your_random_secret_key_here
   ```

3. Generate a secure Flask secret key:
   ```bash
   python -c "import secrets; print(secrets.token_hex(32))"
   ```

### 4. Install Dependencies

```bash
pip install -r requirements.txt
```

### 5. Start the API Server

```bash
python run_api.py
```

## API Endpoints

### Authentication Endpoints

#### Get Clerk Configuration
```bash
GET /api/v1/auth/config
```
Returns the publishable key for frontend integration.

**Response:**
```json
{
  "publishable_key": "pk_test_...",
  "sign_in_url": "/sign-in",
  "sign_up_url": "/sign-up"
}
```

#### Verify Token
```bash
POST /api/v1/auth/verify
Content-Type: application/json

{
  "token": "your_clerk_session_token"
}
```

**Response:**
```json
{
  "valid": true,
  "user": {
    "id": "user_...",
    "email": "user@example.com",
    "metadata": {}
  }
}
```

#### Get Current User
```bash
GET /api/v1/auth/me
Authorization: Bearer <clerk_session_token>
```

**Response:**
```json
{
  "user": {
    "id": "user_...",
    "email": "user@example.com",
    "email_verified": true,
    "metadata": {},
    "created_at": 1234567890
  }
}
```

#### Get Session Info
```bash
GET /api/v1/auth/session
Authorization: Bearer <clerk_session_token>
```

**Response:**
```json
{
  "session": {
    "user_id": "user_...",
    "active": true,
    "expires_at": 1234567890,
    "issued_at": 1234567890
  }
}
```

## Protected Endpoints

All pipeline and module endpoints require authentication:

```bash
POST /api/v1/pipeline/run
Authorization: Bearer <clerk_session_token>
```

## Frontend Integration

### React Example with Clerk

```jsx
import { ClerkProvider, SignIn, SignUp, useAuth } from '@clerk/clerk-react';

function App() {
  return (
    <ClerkProvider publishableKey={process.env.REACT_APP_CLERK_PUBLISHABLE_KEY}>
      <YourApp />
    </ClerkProvider>
  );
}

function ProtectedComponent() {
  const { getToken } = useAuth();
  
  const callAPI = async () => {
    const token = await getToken();
    
    const response = await fetch('http://localhost:5000/api/v1/pipeline/run', {
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${token}`,
        'Content-Type': 'application/json'
      },
      body: JSON.stringify({
        data: [[1, 2, 3]],
        tda_module: 'rips'
      })
    });
    
    return response.json();
  };
  
  return <button onClick={callAPI}>Run Pipeline</button>;
}
```

### Vanilla JavaScript Example

```javascript
// Get Clerk configuration
const configResponse = await fetch('http://localhost:5000/api/v1/auth/config');
const config = await configResponse.json();

// Initialize Clerk (in your HTML)
// <script src="https://cdn.clerk.com/clerk.js"></script>

const clerk = window.Clerk;
await clerk.load({
  publishableKey: config.publishable_key
});

// After user signs in, get the session token
const session = clerk.session;
const token = await session.getToken();

// Use token for API calls
const response = await fetch('http://localhost:5000/api/v1/pipeline/run', {
  method: 'POST',
  headers: {
    'Authorization': `Bearer ${token}`,
    'Content-Type': 'application/json'
  },
  body: JSON.stringify({
    data: [[1, 2, 3]],
    tda_module: 'rips'
  })
});
```

## Development Mode

For local development without Clerk configured, the API accepts test tokens:

```bash
# Any token starting with "test_" will work in development mode
curl -X GET http://localhost:5000/api/v1/auth/me \
  -H "Authorization: Bearer test_dev_token"
```

⚠️ **This only works when `FLASK_ENV=development`**

## Testing

Update your tests to use Clerk tokens or mock the authentication:

```python
import pytest
from unittest.mock import patch

@pytest.fixture
def mock_clerk_auth():
    with patch('api.middleware.auth.verify_clerk_token') as mock:
        mock.return_value = {
            'sub': 'test_user_id',
            'email': 'test@example.com',
            'metadata': {'tier': 'free'}
        }
        yield mock

def test_protected_endpoint(client, mock_clerk_auth):
    response = client.get('/api/v1/auth/me',
                         headers={'Authorization': 'Bearer test_token'})
    assert response.status_code == 200
```

## Security Best Practices

1. ✅ **Never commit `.env` file** - It's in `.gitignore`
2. ✅ **Use environment variables** - All secrets loaded from `.env`
3. ✅ **Rotate keys regularly** - Update Clerk keys periodically
4. ✅ **Use HTTPS in production** - Never send tokens over HTTP
5. ✅ **Set proper CORS** - Restrict origins in production
6. ✅ **Monitor token usage** - Check Clerk dashboard for anomalies

## Troubleshooting

### "CLERK_SECRET_KEY not set"
- Make sure `.env` file exists
- Check that `CLERK_SECRET_KEY` is set in `.env`
- Restart the server after updating `.env`

### "Invalid token"
- Token may be expired (Clerk tokens expire after 1 hour by default)
- User may need to sign in again
- Check that you're using the correct Clerk application keys

### "Token verification failed"
- Ensure you're using the correct secret key for your environment
- Check that the token is from the same Clerk application
- Verify network connectivity to Clerk's servers

## Production Deployment

1. Set environment variables in your hosting platform
2. Use `pk_live_` and `sk_live_` keys (not test keys)
3. Enable HTTPS
4. Configure CORS for your frontend domain
5. Set up monitoring and logging
6. Consider using Clerk's webhook for user events

## Additional Resources

- [Clerk Documentation](https://clerk.com/docs)
- [Clerk React SDK](https://clerk.com/docs/references/react/overview)
- [Clerk Backend API](https://clerk.com/docs/references/backend/overview)
- [JWT Verification](https://clerk.com/docs/backend-requests/handling/manual-jwt)

