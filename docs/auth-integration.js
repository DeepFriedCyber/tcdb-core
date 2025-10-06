/**
 * Auth Integration for Homepage
 * Add this script to docs/index.html
 */

class TCDBAuth {
  constructor() {
    this.apiBase = 'https://tcdb.uk/api';
    this.sessionToken = localStorage.getItem('tcdb_session');
    this.init();
  }

  async init() {
    // Check if we're on verify page
    const urlParams = new URLSearchParams(window.location.search);
    const verifyToken = urlParams.get('token');
    
    if (verifyToken) {
      await this.verifyToken(verifyToken);
      return;
    }

    // Check existing session
    if (this.sessionToken) {
      await this.checkSession();
    }

    this.setupEventListeners();
    this.updateUI();
  }

  setupEventListeners() {
    // Sign In button
    const signInBtn = document.getElementById('sign-in-btn');
    if (signInBtn) {
      signInBtn.addEventListener('click', () => this.showAuthModal('login'));
    }

    // Sign Up / Get API Access button
    const signUpBtn = document.getElementById('sign-up-btn');
    if (signUpBtn) {
      signUpBtn.addEventListener('click', () => this.showAuthModal('signup'));
    }

    // Sign Out button
    const signOutBtn = document.getElementById('sign-out-btn');
    if (signOutBtn) {
      signOutBtn.addEventListener('click', () => this.signOut());
    }

    // Dashboard button
    const dashboardBtn = document.getElementById('dashboard-btn');
    if (dashboardBtn) {
      dashboardBtn.addEventListener('click', () => {
        window.location.href = '/dashboard.html';
      });
    }
  }

  showAuthModal(type) {
    const modal = document.getElementById('auth-modal');
    const title = document.getElementById('auth-modal-title');
    const subtitle = document.getElementById('auth-modal-subtitle');
    const submitBtn = document.getElementById('auth-submit-btn');

    if (type === 'login') {
      title.textContent = 'Welcome Back';
      subtitle.textContent = 'Enter your email to receive a magic link';
      submitBtn.textContent = 'Send Login Link';
    } else {
      title.textContent = 'Get Started';
      subtitle.textContent = 'Enter your email to create your account';
      submitBtn.textContent = 'Get API Access';
    }

    modal.classList.remove('hidden');
    modal.dataset.authType = type;
  }

  hideAuthModal() {
    const modal = document.getElementById('auth-modal');
    modal.classList.add('hidden');
    document.getElementById('auth-email-input').value = '';
    document.getElementById('auth-error').classList.add('hidden');
    document.getElementById('auth-success').classList.add('hidden');
  }

  async submitAuth() {
    const modal = document.getElementById('auth-modal');
    const type = modal.dataset.authType;
    const email = document.getElementById('auth-email-input').value;
    const errorDiv = document.getElementById('auth-error');
    const successDiv = document.getElementById('auth-success');
    const submitBtn = document.getElementById('auth-submit-btn');

    errorDiv.classList.add('hidden');
    successDiv.classList.add('hidden');

    if (!email || !this.isValidEmail(email)) {
      errorDiv.textContent = 'Please enter a valid email address';
      errorDiv.classList.remove('hidden');
      return;
    }

    submitBtn.disabled = true;
    submitBtn.textContent = 'Sending...';

    try {
      const endpoint = type === 'login' ? '/auth/login' : '/auth/signup';
      const response = await fetch(`${this.apiBase}${endpoint}`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ email })
      });

      const data = await response.json();

      if (!response.ok) {
        throw new Error(data.error || 'Authentication failed');
      }

      // Show success message
      successDiv.textContent = `Check your email! We sent a magic link to ${email}`;
      successDiv.classList.remove('hidden');

      // For development: auto-verify (remove in production)
      if (data.magicLink) {
        console.log('Magic link:', data.magicLink);
        setTimeout(() => {
          const token = new URL(data.magicLink).searchParams.get('token');
          this.verifyToken(token);
        }, 2000);
      }

    } catch (error) {
      errorDiv.textContent = error.message;
      errorDiv.classList.remove('hidden');
    } finally {
      submitBtn.disabled = false;
      submitBtn.textContent = type === 'login' ? 'Send Login Link' : 'Get API Access';
    }
  }

  async verifyToken(token) {
    try {
      const response = await fetch(`${this.apiBase}/auth/verify`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ token })
      });

      const data = await response.json();

      if (!response.ok) {
        throw new Error(data.error || 'Verification failed');
      }

      // Store session
      this.sessionToken = data.sessionToken;
      localStorage.setItem('tcdb_session', data.sessionToken);
      localStorage.setItem('tcdb_user', JSON.stringify(data.user));

      // Redirect to dashboard
      window.location.href = '/dashboard.html';

    } catch (error) {
      alert('Verification failed: ' + error.message);
      window.location.href = '/';
    }
  }

  async checkSession() {
    try {
      const response = await fetch(`${this.apiBase}/keys`, {
        headers: {
          'Authorization': `Bearer ${this.sessionToken}`
        }
      });

      if (!response.ok) {
        // Session invalid
        this.signOut();
        return;
      }

      const data = await response.json();
      localStorage.setItem('tcdb_user', JSON.stringify(data));

    } catch (error) {
      this.signOut();
    }
  }

  signOut() {
    localStorage.removeItem('tcdb_session');
    localStorage.removeItem('tcdb_user');
    this.sessionToken = null;
    window.location.href = '/';
  }

  updateUI() {
    const signedOutBtns = document.getElementById('auth-buttons-signed-out');
    const signedInBtns = document.getElementById('auth-buttons-signed-in');

    if (this.sessionToken) {
      signedOutBtns?.classList.add('hidden');
      signedInBtns?.classList.remove('hidden');
    } else {
      signedOutBtns?.classList.remove('hidden');
      signedInBtns?.classList.add('hidden');
    }
  }

  isValidEmail(email) {
    return /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email);
  }
}

// Initialize auth when DOM is ready
if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', () => {
    window.tcdbAuth = new TCDBAuth();
  });
} else {
  window.tcdbAuth = new TCDBAuth();
}

// Export for use in modal
window.submitAuth = () => window.tcdbAuth.submitAuth();
window.hideAuthModal = () => window.tcdbAuth.hideAuthModal();

