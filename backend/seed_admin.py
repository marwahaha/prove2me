"""
Script to seed an admin user.
Run with: python seed_admin.py
"""
import sys
sys.path.insert(0, '.')

from app.database import SessionLocal
from app.models import User
from app.auth import hash_password


def seed_admin():
    db = SessionLocal()

    # Check if admin already exists
    admin = db.query(User).filter(User.username == "admin").first()
    if admin:
        print("Admin user already exists")
        return

    # Create admin user
    admin = User(
        username="admin",
        email="admin@prove2me.local",
        password_hash=hash_password("admin123"),  # Change this in production!
        is_admin=True,
        is_approved=True,
        points=0,
    )
    db.add(admin)
    db.commit()
    print("Admin user created successfully")
    print("Username: admin")
    print("Password: admin123")
    print("IMPORTANT: Change this password in production!")


if __name__ == "__main__":
    seed_admin()
