-- Created for PostgreSQL 11

DROP TABLE IF EXISTS timers, cronjobs, staff_roles, userlogs, user_restrictions, tags, commands_usage, bug_tickets, toggleable_roles;

-- Just store the timestamps as utcnow(). 
-- Makes my life easier
CREATE TABLE IF NOT EXISTS timers
(
    id SERIAL PRIMARY KEY,
    expiry timestamp without time zone,
    created timestamp without time zone DEFAULT (now() at time zone 'utc'),
    event TEXT,
    extra JSONB
);

CREATE TABLE IF NOT EXISTS staff_roles
(
    guild_id BIGINT NOT NULL,
    role_id BIGINT NOT NULL,
    perms TEXT NOT NULL,
    CONSTRAINT staff_roles_pkey PRIMARY KEY (guild_id, role_id, perms)
);

CREATE TABLE IF NOT EXISTS userlogs
(
    guild_id BIGINT PRIMARY KEY,
    userlog JSONB
);

CREATE TABLE IF NOT EXISTS user_restrictions
(
    guild_id BIGINT NOT NULL,
    user_id BIGINT NOT NULL,
    role_id BIGINT NOT NULL,
    CONSTRAINT user_restrictions_pkey PRIMARY KEY (guild_id, user_id, role_id)
);

CREATE TABLE IF NOT EXISTS guild_mod_config
(
    guild_id BIGINT PRIMARY KEY,
    mute_role_id BIGINT,
    log_channels JSONB
);

CREATE TABLE IF NOT EXISTS toggleable_roles
(
    guild_id BIGINT NOT NULL,
    role_id BIGINT NOT NULL,
    CONSTRAINT toggleable_roles_pkey PRIMARY KEY (guild_id, role_id)
);

CREATE TABLE IF NOT EXISTS auto_roles
(
    guild_id BIGINT NOT NULL,
    role_id BIGINT NOT NULL,
    CONSTRAINT auto_roles_pkey PRIMARY KEY (guild_id, role_id)
);

CREATE TABLE IF NOT EXISTS tags
(
    guild_id BIGINT PRIMARY KEY,
    tag_name TEXT,
    tag_content TEXT,
    tag_author BIGINT,
    created_at TIMESTAMP WITHOUT TIME ZONE,
    usage BIGINT
);

CREATE TABLE IF NOT EXISTS tag_aliases
(
    guild_id BIGINT PRIMARY KEY,
    tag_name TEXT,
    tag_points_to TEXT REFERENCES tags(tag_name) ON DELETE CASCADE,
    tag_author BIGINT,
    created_at TIMESTAMP WITHOUT TIME ZONE
);

CREATE TABLE IF NOT EXISTS commands_usage
(
    id BIGSERIAL PRIMARY KEY,
    guild_id BIGINT,
    user_id BIGINT,
    used_at TIMESTAMP WITHOUT TIME ZONE,-- DEFAULT (now() at time zone 'utc'),
    command_name TEXT,
    failure BOOLEAN
);

CREATE INDEX IF NOT EXISTS commands_usage_guild_id_idx ON commands_usage (guild_id);
CREATE INDEX IF NOT EXISTS commands_usage_user_id_idx ON commands_usage (user_id);
CREATE INDEX IF NOT EXISTS commands_usage_used_at_idx ON commands_usage (used_at);
CREATE INDEX IF NOT EXISTS commands_usage_command_name_idx ON commands_usage (command_name);

CREATE TABLE IF NOT EXISTS bug_tickets
(
    id SERIAL PRIMARY KEY,
    guild_id BIGINT,
    channel_id BIGINT,
    message_id BIGINT,
    status TEXT,
    created TIMESTAMP WITHOUT TIME ZONE,
    ticket_info JSONB
);

CREATE TABLE IF NOT EXISTS modlog_cases
(
    guild_id BIGINT PRIMARY KEY,
    channel_id BIGINT,
    message_id BIGINT,
    case_id SERIAL,
    case_info JSONB
);