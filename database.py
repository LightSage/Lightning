from sqlalchemy import Column, Integer, String, ForeignKey
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy.orm import relationship
from sqlalchemy import create_engine

Base = declarative_base()


class StaffRoles(Base):
    __tablename__ = "staff_roles"
    guild_id = Column(Integer, primary_key=True)
    role_id = Column(Integer, primary_key=True)
    staff_perms = Column(String, primary_key=True)