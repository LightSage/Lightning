-- 3.0.0 Migration
-- depends: 

-- Convert warns to infractions
INSERT INTO infractions (guild_id, user_id, moderator_id, created_at, reason)
SELECT guild_id, user_id, mod_id, timestamp, reason FROM warns;