# Prove2Me - Lean Proof Submission Platform

A web platform where users submit Lean statements (problems) and other users submit proofs. Features a points/prize system with leaderboard and admin controls.

## Features

- **Submit Lean Statements**: Users can submit Lean 4 statements (with `sorry` allowed)
- **Submit Proofs**: Other users can submit proofs (no `sorry` allowed)
- **Prize System**: Prizes grow exponentially over time
- **Leaderboard**: Track top provers
- **Admin Panel**: User approval, prize settings management
- **Mathlib Support**: Full access to Mathlib library

## Tech Stack

- **Backend**: FastAPI (Python)
- **Frontend**: React with TypeScript
- **Database**: PostgreSQL
- **Lean**: Lean 4 with Mathlib

## Prerequisites

- Python 3.11+
- Node.js 18+
- PostgreSQL
- Lean 4 with `lake` available in PATH

## Setup

### 1. Set up Lean 4 Project with Mathlib

```bash
# Create a Lean 4 project with Mathlib
lake +leanprover-lean4:v4.x.0 new prove2me_lean math
cd prove2me_lean
lake update
lake build  # Initial build (takes time)
```

### 2. Set up PostgreSQL Database

```bash
# Create database
createdb prove2me

# Or with psql
psql -c "CREATE DATABASE prove2me;"
```

### 3. Backend Setup

```bash
cd backend

# Create virtual environment
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate

# Install dependencies
pip install -r requirements.txt

# Create .env file
cp .env.example .env
# Edit .env with your settings:
# - DATABASE_URL
# - SECRET_KEY (generate a secure random string)
# - LEAN_PROJECT_PATH (path to your prove2me_lean project)

# Run database migrations
alembic upgrade head

# Seed admin user
python seed_admin.py

# Start the backend
uvicorn app.main:app --reload --port 8000
```

### 4. Frontend Setup

```bash
cd frontend

# Install dependencies
npm install

# Start development server
npm run dev
```

The frontend will be available at http://localhost:5173

## Default Admin Credentials

- Username: `admin`
- Password: `admin123`

**IMPORTANT**: Change the admin password in production!

## API Endpoints

### Authentication
- `POST /api/auth/register` - Register new account (requires approval)
- `POST /api/auth/login` - Login (requires approved account)
- `POST /api/auth/logout` - Logout
- `GET /api/auth/me` - Get current user

### Statements
- `GET /api/statements` - List unproven statements
- `GET /api/statements/{id}` - Get statement details
- `POST /api/statements` - Submit new statement
- `GET /api/statements/my` - List user's own statements
- `POST /api/statements/compile` - Test compile code

### Proofs
- `POST /api/proofs/{statement_id}` - Submit proof for statement

### Leaderboard
- `GET /api/leaderboard` - Get ranked users

### Admin
- `GET /api/admin/pending-users` - List unapproved users
- `POST /api/admin/approve-user/{id}` - Approve user
- `DELETE /api/admin/reject-user/{id}` - Reject user
- `GET /api/admin/settings` - Get prize settings
- `PUT /api/admin/settings` - Update prize settings
- `GET /api/admin/all-statements` - Get all statements
- `GET /api/admin/users` - Get all users

## Prize Calculation

The prize for a statement grows exponentially over time:

```
prize = base_points * (growth_rate ^ days_elapsed)
```

Default settings:
- Base Points: 100
- Growth Rate: 1.50 (50% per day)
- Submitter Share: 20%

When a proof is accepted:
- 80% of prize goes to the prover
- 20% of prize goes to the statement submitter

## Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| DATABASE_URL | PostgreSQL connection URL | postgresql://postgres:postgres@localhost:5432/prove2me |
| SECRET_KEY | JWT signing secret | (required) |
| LEAN_PROJECT_PATH | Path to Lean 4 project with Mathlib | (required) |
| LEAN_TIMEOUT | Compilation timeout in seconds | 30 |

## Project Structure

```
prove2me/
├── backend/
│   ├── app/
│   │   ├── main.py              # FastAPI app entry
│   │   ├── config.py            # Settings & env vars
│   │   ├── database.py          # PostgreSQL connection
│   │   ├── models.py            # SQLAlchemy models
│   │   ├── schemas.py           # Pydantic schemas
│   │   ├── auth.py              # Authentication logic
│   │   ├── lean_runner.py       # Lean compilation service
│   │   ├── prize.py             # Prize calculation
│   │   └── routers/
│   │       ├── auth.py          # Login/register/logout
│   │       ├── statements.py    # Submit/list statements
│   │       ├── proofs.py        # Submit proofs
│   │       ├── leaderboard.py   # Points leaderboard
│   │       └── admin.py         # Admin controls
│   ├── alembic/                 # Database migrations
│   ├── requirements.txt
│   └── seed_admin.py
├── frontend/
│   ├── src/
│   │   ├── App.tsx
│   │   ├── api/                 # API client
│   │   ├── components/          # Reusable components
│   │   ├── pages/               # Page components
│   │   └── contexts/            # Auth context
│   ├── package.json
│   └── vite.config.ts
└── README.md
```

## Verification Steps

1. Create test admin account, approve it
2. Register new user, verify needs approval
3. Admin approves user, user can now login
4. Submit a Lean statement (with sorry), verify it compiles
5. Different user submits valid proof, verify points distributed
6. Check leaderboard shows updated points
7. Admin changes prize settings, verify new prizes reflect changes

## License

MIT
