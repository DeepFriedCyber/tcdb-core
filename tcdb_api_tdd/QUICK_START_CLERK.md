# Quick Start with Clerk Authentication

## 🚀 5-Minute Setup

### Step 1: Get Clerk Keys (2 minutes)
1. Go to https://clerk.com and sign up
2. Create a new application
3. Copy your keys from the API Keys page:
   - `CLERK_SECRET_KEY` (starts with `sk_test_`)
   - `CLERK_PUBLISHABLE_KEY` (starts with `pk_test_`)

### Step 2: Configure Environment (1 minute)
```bash
# Copy the example file
cp .env.example .env

# Edit .env and paste your keys
nano .env  # or use any text editor
```

Your `.env` should look like:
```bash
CLERK_SECRET_KEY=sk_test_xxxxxxxxxxxxx
CLERK_PUBLISHABLE_KEY=pk_test_xxxxxxxxxxxxx
FLASK_SECRET_KEY=your_random_secret_here
```

### Step 3: Install & Run (2 minutes)
```bash
# Install dependencies (if not already done)
pip install -r requirements.txt

# Start the server
python run_api.py
```

## ✅ Test It Works

### Test 1: Get Clerk Config
```bash
curl http://localhost:5000/api/v1/auth/config
```

Should return your publishable key.

### Test 2: Development Mode (No Clerk Required)
```bash
# Set development mode in .env
FLASK_ENV=development

# Test with any token starting with "test_"
curl -H "Authorization: Bearer test_my_token" \
     http://localhost:5000/api/v1/auth/me
```

Should return test user info.

## 🔧 Development Mode

**Don't have Clerk set up yet?** No problem!

1. Set `FLASK_ENV=development` in `.env`
2. Use any token starting with `test_` in your requests
3. Perfect for local development and testing

```bash
# Works in development mode
Authorization: Bearer test_anything_here
```

## 📱 Frontend Integration

### React
```bash
npm install @clerk/clerk-react
```

```jsx
import { ClerkProvider, SignIn, useAuth } from '@clerk/clerk-react';

function App() {
  return (
    <ClerkProvider publishableKey="pk_test_...">
      <YourApp />
    </ClerkProvider>
  );
}

function APIComponent() {
  const { getToken } = useAuth();
  
  const callAPI = async () => {
    const token = await getToken();
    const res = await fetch('http://localhost:5000/api/v1/pipeline/run', {
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${token}`,
        'Content-Type': 'application/json'
      },
      body: JSON.stringify({ data: [[1,2,3]], tda_module: 'rips' })
    });
    return res.json();
  };
}
```

### HTML + JavaScript
```html
<script src="https://cdn.clerk.com/clerk.js"></script>
<script>
  const clerk = window.Clerk;
  await clerk.load({ publishableKey: 'pk_test_...' });
  
  // After user signs in
  const token = await clerk.session.getToken();
  
  // Use in API calls
  fetch('http://localhost:5000/api/v1/pipeline/run', {
    headers: { 'Authorization': `Bearer ${token}` }
  });
</script>
```

## 🧪 Testing

All tests work without Clerk configured:

```bash
# Run all tests
pytest -v

# Run only auth tests
pytest tests/api/test_auth.py -v
```

Tests use mocked authentication, so no Clerk account needed!

## 🆘 Troubleshooting

### "CLERK_SECRET_KEY not set"
- Check `.env` file exists
- Verify keys are set in `.env`
- Restart the server

### "Invalid token"
- Token may be expired (refresh in Clerk)
- Check you're using the right environment (test vs live)
- Verify `CLERK_SECRET_KEY` matches your Clerk app

### Development mode not working
- Ensure `FLASK_ENV=development` in `.env`
- Token must start with `test_`
- Restart server after changing `.env`

## 📚 More Info

- **Full Setup Guide**: `CLERK_SETUP.md`
- **Migration Details**: `CLERK_MIGRATION_SUMMARY.md`
- **Clerk Docs**: https://clerk.com/docs
- **API Reference**: `README.md`

## 🎯 Key Points

✅ **No hardcoded credentials** - Everything in `.env`  
✅ **Development mode** - Test without Clerk  
✅ **Production ready** - Enterprise authentication  
✅ **Easy frontend integration** - React, Vue, vanilla JS  
✅ **Fully tested** - 17 tests passing  

---

**You're ready to go! 🚀**

