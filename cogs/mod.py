# Lightning.py - The Successor to Lightning.js
# Copyright (C) 2019 - LightSage
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as published
# by the Free Software Foundation at version 3 of the License.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Affero General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.
#
# In addition, clauses 7b and 7c are in effect for this program.
#
# b) Requiring preservation of specified reasonable legal notices or
# author attributions in that material or in the Appropriate Legal
# Notices displayed by works containing it; or
#
# c) Prohibiting misrepresentation of the origin of that material, or
# requiring that modified versions of such material be marked in
# reasonable ways as different from the original version

import discord
from discord.ext import commands
from utils.user_log import userlog
from utils.user_log import get_userlog, set_userlog, userlog_event_types
from utils.checks import is_staff_or_has_perms, member_at_least_has_staff_role
from datetime import datetime, timedelta
import json
# import asyncio
from utils.time import natural_timedelta, FutureTime
import io
from bolt.paginator import Pages
from utils.converters import TargetMember, WarnNumber
from utils.errors import TimersUnavailable, MuteRoleError
from bolt.time import get_utc_timestamp

# Most Commands Taken From Robocop-NG. MIT Licensed
# https://github.com/aveao/robocop-ng/blob/master/cogs/mod.py


class WarnPages(Pages):
    """Similar to FieldPages except entries should be a list of
    tuples having (key, value) to show as embed fields instead.
    """
    def __init__(self, set_author, ctx, entries, *, per_page=4):
        super().__init__(ctx, entries=entries, per_page=per_page)
        self.set_author = set_author

    def prepare_embed(self, entries, page, *, first=False):
        self.embed.clear_fields()
        self.embed.description = discord.Embed.Empty
        self.embed.set_author(name=self.set_author)

        for key, value in entries:
            self.embed.add_field(name=key, value=value, inline=False)

        if self.maximum_pages > 1:
            if self.show_entry_count:
                text = f'Page {page}/{self.maximum_pages} ({len(self.entries)} entries)'
            else:
                text = f'Page {page}/{self.maximum_pages}'

            self.embed.set_footer(text=text)


class Mod(commands.Cog):
    """
    Moderation and server management commands.
    """
    def __init__(self, bot):
        self.bot = bot

    async def cog_check(self, ctx):
        if ctx.guild is None:
            raise commands.NoPrivateMessage()
        return True

    def mod_reason(self, ctx, reason: str):
        if reason:
            to_return = f"{ctx.author} (ID: {ctx.author.id}): {reason}"
        else:
            to_return = f"Action done by {ctx.author} (ID: {ctx.author.id})"
        if len(to_return) > 512:
            raise commands.BadArgument('Reason is too long!')
        return to_return

    async def log_send(self, ctx, message, **kwargs):
        query = """SELECT log_channels FROM guild_mod_config
                   WHERE guild_id=$1;
                """
        ret = await self.bot.db.fetchval(query, ctx.guild.id)
        if ret:
            guild_config = json.loads(ret)
        else:
            guild_config = {}

        if "modlog_chan" in guild_config:
            try:
                log_channel = self.bot.get_channel(guild_config["modlog_chan"])
                await log_channel.send(content=message, **kwargs)
            except discord.Forbidden:
                pass

    async def purged_log_send(self, ctx, file_to_send):
        query = """SELECT * FROM guild_mod_config
                   WHERE guild_id=$1;
                """
        ret = await self.bot.db.fetchrow(query, ctx.guild.id)
        if ret['log_channels']:
            guild_config = json.loads(ret['log_channels'])
        else:
            guild_config = {}

        if "modlog_chan" in guild_config:
            try:
                log_channel = self.bot.get_channel(guild_config["modlog_chan"])
                await log_channel.send(file=file_to_send)
            except discord.Forbidden:
                pass

    async def logid_send(self, guild_id: int, message, **kwargs):
        """Async Function to use a provided guild ID instead of relying
        on context (ctx). This is more for being used for Mod Log Cases"""
        query = """SELECT log_channels FROM guild_mod_config
                   WHERE guild_id=$1;
                """
        ret = await self.bot.db.fetchval(query, guild_id)
        if ret:
            guild_config = json.loads(ret)
        else:
            guild_config = {}

        if "modlog_chan" in guild_config:
            try:
                log_channel = self.bot.get_channel(guild_config["modlog_chan"])
                msg = await log_channel.send(message, **kwargs)
                return msg
            except KeyError:
                pass

    async def set_user_restrictions(self, guild_id: int, user_id: int, role_id: int):
        query = """INSERT INTO user_restrictions (guild_id, user_id, role_id)
                   VALUES ($1, $2, $3)
                   ON CONFLICT (guild_id, user_id, role_id)
                   DO UPDATE SET guild_id = EXCLUDED.guild_id,
                   role_id = EXCLUDED.role_id,
                   user_id = EXCLUDED.user_id;
                """
        con = await self.bot.db.acquire()
        try:
            await con.execute(query, guild_id, user_id, role_id)
        finally:
            await self.bot.db.release(con)

    async def remove_user_restriction(self, guild_id: int,
                                      user_id: int, role_id: int):
        query = """DELETE FROM user_restrictions
                   WHERE guild_id=$1
                   AND user_id=$2
                   AND role_id=$3;
                """
        con = await self.bot.db.acquire()
        try:
            await con.execute(query, guild_id, user_id, role_id)
        finally:
            await self.bot.db.release(con)

    async def add_modlog_entry(self, guild_id, action: str, mod, target, reason: str):
        """Adds a case to the mod log

        Arguments:
        --------------
        guild_id: `int`
            The guild id of where the action was done.
        action: `str`
            The type of action that was done.
            Actions can be one of the following: Ban, Kick, Mute, Unmute, Unban, Warn
        mod:
            The responsible moderator who did the action
        target:
            The member that got an action taken against them
        reason: `str`
            The reason why an action was taken
        """
        safe_name = await commands.clean_content().convert(self.bot, str(target))
        if action == "Ban":
            message = f"⛔ **Ban**: {mod.mention} banned "\
                      f"{target.mention} | {safe_name}\n"\
                      f"🏷 __User ID__: {target.id}\n"
        elif action == "Kick":
            message = f"👢 **Kick**: {mod.mention} kicked "\
                      f"{target.mention} | {safe_name}\n"\
                      f"🏷 __User ID__: {target.id}\n"
        # Send the initial message then edit it with our reason.
        if reason:
            message += f"\N{PENCIL} __Reason__: \"{reason}\""
        else:
            message += f"*Responsible moderator* please add a reason to the case."\
                       f" `l.case "

    # @commands.Cog.listener()
    # async def on_member_ban(self, guild, user):
        # Wait for Audit Log to update
    #    await asyncio.sleep(0.5)
        # Cap off at 25 for safety measures
    #    async for entry in guild.audit_logs(limit=25, action=discord.AuditLogAction.ban):
    #        if entry.target == user:
    #            author = entry.user
    #            reason = entry.reason if entry.reason else ""
    #            break
        #  If author of the entry is the bot itself, don't log since
        #  this would've been already logged.
    #    if entry.target.id != self.bot.user.id:
    #        await self.add_modlog_entry(guild.id, "Ban", author, user, reason)

    async def purged_txt(self, ctx, limit):

        """Makes a file containing the limit of messages purged."""
        log_t = f"Archive of {ctx.channel} (ID: {ctx.channel.id}) "\
                f"made on {datetime.utcnow()}\n\n\n"
        async for log in ctx.channel.history(limit=limit):
            # .strftime('%X/%H:%M:%S') but no for now
            log_t += f"[{log.created_at}]: {log.author} - {log.clean_content}"
            if log.attachments:
                for attach in log.attachments:
                    log_t += f"{attach.url}\n"
            else:
                log_t += "\n"

        aiostring = io.StringIO()
        aiostring.write(log_t)
        aiostring.seek(0)
        aiofile = discord.File(aiostring, filename=f"{ctx.channel}_archive.txt")
        return aiofile

    @commands.guild_only()  # This isn't needed but w/e :shrugkitty:
    @commands.bot_has_permissions(kick_members=True)
    @is_staff_or_has_perms("Moderator", kick_members=True)
    @commands.command()
    async def kick(self, ctx, target: TargetMember, *, reason: str = ""):
        """Kicks a user.

        In order to use this command, you must either have
        Kick Members permission or a role that
        is assigned as a Moderator or above in the bot."""

        safe_name = await commands.clean_content().convert(ctx, str(target))

        dm_message = f"You were kicked from {ctx.guild.name}."
        if reason:
            dm_message += f" The given reason is: \"{reason}\"."
        dm_message += "\n\nYou are able to rejoin the server," \
                      " but please be sure to behave when participating again."

        try:
            await target.send(dm_message)
        except discord.errors.Forbidden:
            # Prevents kick issues in cases where user blocked bot
            # or has DMs disabled
            pass
        await ctx.guild.kick(target, reason=f"{self.mod_reason(ctx, reason)}")
        await ctx.send(f"{target} has been kicked. 👌 ")
        chan_message = f"👢 **Kick**: {ctx.author.mention} kicked " \
                       f"{target.mention} | {safe_name}\n" \
                       f"🏷 __User ID__: {target.id}\n"
        if reason:
            chan_message += f"\N{PENCIL} __Reason__: \"{reason}\""
        else:
            chan_message += f"\nPlease add an explanation below. In the future" \
                            f", it is recommended to use " \
                            f"`{ctx.prefix}kick <user> [reason]`" \
                            f" as the reason is automatically sent to the user."
        await self.log_send(ctx, chan_message)

    @commands.guild_only()  # This isn't needed but w/e :shrugkitty:
    @commands.bot_has_permissions(ban_members=True)
    @is_staff_or_has_perms("Moderator", ban_members=True)
    @commands.command()
    async def ban(self, ctx, target: TargetMember, *, reason: str = ""):
        """Bans a user.

        In order to use this command, you must either have
        Ban Members permission or a role that
        is assigned as a Moderator or above in the bot."""

        safe_name = await commands.clean_content().convert(ctx, str(target))

        dm_message = f"You were banned from {ctx.guild.name}."
        if reason:
            dm_message += f" The given reason is: \"{reason}\"."
        dm_message += "\n\nThis ban does not expire."
        dm_message += "\n\nIf you believe this to be in error, please message the staff."

        try:
            await target.send(dm_message)
        except discord.errors.Forbidden:
            # Prevents ban issues in cases where user blocked bot
            # or has DMs disabled
            pass

        await ctx.guild.ban(target, reason=f"{self.mod_reason(ctx, reason)}",
                            delete_message_days=0)
        await ctx.safe_send(f"{target} is now b&. 👍")
        chan_message = f"⛔ **Ban**: {ctx.author.mention} banned " \
                       f"{target.mention} | {safe_name}\n" \
                       f"🏷 __User ID__: {target.id}\n"
        if reason:
            chan_message += f"\N{PENCIL} __Reason__: \"{reason}\""
        else:
            chan_message += f"\nPlease add an explanation below. In the future" \
                            f", it is recommended to use `{ctx.prefix}ban <user> [reason]`" \
                            f" as the reason is automatically sent to the user."
        await self.log_send(ctx, chan_message)

    async def warn_settings(self, guild_id):
        """Returns the warn settings for a guild"""
        query = """SELECT warn_ban, warn_kick
                   FROM guild_mod_config
                   WHERE guild_id=$1;"""
        ret = await self.bot.db.fetchrow(query, guild_id)
        if ret:
            return ret
        else:
            return None

    async def warn_count_check(self, ctx, target, reason: str = ""):
        msg = f"You were warned on {ctx.guild.name}."
        if reason:
            msg += " The given reason is: " + reason
        warn_count = await userlog(self.bot, ctx.guild, target.id,
                                   ctx.author, reason,
                                   "warns", target.name)
        msg += f"\n\nThis is warn #{warn_count}."
        punishable_warn = await self.warn_settings(ctx.guild.id)
        if not punishable_warn:
            try:
                await target.send(msg)
                return warn_count
            except discord.errors.Forbidden:
                return warn_count
        if punishable_warn['warn_kick']:
            if warn_count == punishable_warn['warn_kick'] - 1:
                msg += " __The next warn will automatically kick.__"
            if warn_count == punishable_warn['warn_kick']:
                msg += "\n\nYou were kicked because of this warning. " \
                       "You can join again right away. "
        if punishable_warn['warn_ban']:
            if warn_count == punishable_warn['warn_ban'] - 1:
                msg += "This is your final warning. " \
                       "Do note that " \
                       "**one more warn will result in a ban**."
            if warn_count >= punishable_warn['warn_ban']:
                msg += f"\n\nYou were automatically banned due to reaching "\
                       f"the guild's warn ban limit of "\
                       f"{punishable_warn['warn_ban']} warnings."
                msg += "\nIf you believe this to be in error, please message the staff."
        try:
            await target.send(msg)
        except discord.errors.Forbidden:
            # Prevents log issues in cases where user blocked bot
            # or has DMs disabled
            pass
        if punishable_warn['warn_kick']:
            if warn_count == punishable_warn['warn_kick']:
                opt_reason = f"[WarnKick] Reached {warn_count} warns. "
                if reason:
                    opt_reason += f"{reason}"
                await ctx.guild.kick(target, reason=f"{self.mod_reason(ctx, opt_reason)}")
        if punishable_warn['warn_ban']:
            if warn_count >= punishable_warn['warn_ban']:  # just in case
                opt_reason = f"[WarnBan] Exceeded WarnBan Limit ({warn_count}). "
                if reason:
                    opt_reason += f"{reason}"
                await ctx.guild.ban(target, reason=f"{self.mod_reason(ctx, opt_reason)}",
                                    delete_message_days=0)
        return warn_count

    @commands.guild_only()
    @commands.bot_has_permissions(kick_members=True, ban_members=True)
    @is_staff_or_has_perms("Helper", manage_messages=True)
    @commands.group(invoke_without_command=True)
    async def warn(self, ctx, target: TargetMember, *, reason: str = ""):
        """Warns a user.

        In order to use this command, you must either have
        Manage Messages permission or a role
        that is assigned as a Helper or above in the bot."""
        warn_count = await self.warn_count_check(ctx, target, reason)

        await ctx.send(f"{target.mention} warned. "
                       f"User has {warn_count} warning(s).")
        safe_name = await commands.clean_content().convert(ctx, str(target))
        msg = f"\N{WARNING SIGN} **Warned**: "\
              f"{ctx.author.mention} warned {target.mention}" \
              f" (warn #{warn_count}) | {safe_name}\n"

        if reason:
            msg += f"\N{PENCIL} __Reason__: \"{reason}\""
        else:
            msg += f"\nPlease add an explanation below. In the future" \
                   f", it is recommended to use `{ctx.prefix}warn <user> [reason]`" \
                   f" as the reason is automatically sent to the user."
        await self.log_send(ctx, msg)

    @commands.guild_only()
    @commands.bot_has_permissions(kick_members=True, ban_members=True)
    @is_staff_or_has_perms("Admin", manage_guild=True)
    @warn.group(name="punishments", aliases=['punishment'])
    async def warn_punish(self, ctx):
        """Configures warn punishments for the server.

        In order to use this command, you must either have
        Manage Guild permission or a role that
        is assigned as a Admin or above in the bot."""
        if ctx.invoked_subcommand is None:
            query = '''SELECT warn_kick, warn_ban
                       FROM guild_mod_config
                       WHERE guild_id=$1;'''
            ret = await self.bot.db.fetchrow(query, ctx.guild.id)
            if not ret['warn_kick'] or ret['warn_ban']:
                return await ctx.send("Warn punishments have not been setup.")
            msg = ""
            if ret['warn_kick']:
                msg += f"Kick: at {ret['warn_kick']} warns\n"
            if ret['warn_ban']:
                msg += f"Ban: at {ret['warn_ban']}+ warns\n"
            return await ctx.send(msg)

    @commands.guild_only()
    @commands.bot_has_permissions(kick_members=True, ban_members=True)
    @is_staff_or_has_perms("Admin", manage_guild=True)
    @warn_punish.command(name="kick")
    async def warn_kick(self, ctx, number: WarnNumber):
        """Configures the warn kick punishment.

        This kicks the member after acquiring a certain amount of warns.

        In order to use this command, you must either have
        Manage Guild permission or a role that
        is assigned as a Admin or above in the bot."""
        query = """SELECT warn_ban
                   FROM guild_mod_config
                   WHERE guild_id=$1;"""
        ban_count = await self.bot.db.fetchval(query, ctx.guild.id)
        if ban_count:
            if number >= ban_count:
                return await ctx.send("You cannot set the same or a higher value "
                                      "for warn kick punishment "
                                      "as the warn ban punishment.")
        query = """INSERT INTO guild_mod_config (guild_id, warn_kick)
                   VALUES ($1, $2)
                   ON CONFLICT (guild_id)
                   DO UPDATE SET warn_kick = EXCLUDED.warn_kick;
                """
        await self.bot.db.execute(query, ctx.guild.id, number)
        await ctx.send(f"Users will now get kicked if they reach "
                       f"{number} warns.")

    @commands.guild_only()
    @commands.bot_has_permissions(kick_members=True, ban_members=True)
    @is_staff_or_has_perms("Admin", manage_guild=True)
    @warn_punish.command(name="ban")
    async def warn_ban(self, ctx, number: WarnNumber):
        """Configures the warn ban punishment.

        This bans the member after acquiring a certain
        amount of warns or higher.

        In order to use this command, you must either have
        Manage Guild permission or a role that
        is assigned as a Admin or above in the bot."""
        query = """SELECT warn_kick
                   FROM guild_mod_config
                   WHERE guild_id=$1;"""
        kick_count = await self.bot.db.fetchval(query, ctx.guild.id)
        if kick_count:
            if number <= kick_count:
                return await ctx.send("You cannot set the same or a lesser value "
                                      "for warn ban punishment "
                                      "as the warn kick punishment.")
        query = """INSERT INTO guild_mod_config (guild_id, warn_ban)
                   VALUES ($1, $2)
                   ON CONFLICT (guild_id)
                   DO UPDATE SET warn_ban = EXCLUDED.warn_ban;
                """
        await self.bot.db.execute(query, ctx.guild.id, number)
        await ctx.send(f"Users will now get banned if they reach "
                       f"{number} or a higher amount of warns.")

    @commands.guild_only()
    @commands.bot_has_permissions(kick_members=True, ban_members=True)
    @is_staff_or_has_perms("Admin", manage_guild=True)
    @warn_punish.command(name="clear")
    async def warn_remove(self, ctx):
        """Removes all warn punishment configuration.

        In order to use this command, you must either have
        Manage Guild permission or a role that
        is assigned as a Admin or above in the bot."""
        query = """UPDATE guild_mod_config
                   SET warn_ban=NULL,
                   warn_kick=NULL
                   WHERE guild_id=$1;
                """
        await self.bot.db.execute(query, ctx.guild.id)
        await ctx.send("Removed warn punishment configuration!")

    @commands.guild_only()
    @commands.bot_has_permissions(manage_messages=True)
    @is_staff_or_has_perms("Moderator", manage_messages=True)
    @commands.command()
    async def purge(self, ctx, message_count: int, *, reason: str = ""):
        """Purges a channel's last x messages.

        In order to use this command, You must either have
        Manage Messages permission or a role that
        is assigned as a Moderator or above in the bot."""
        if message_count > 100:
            return await ctx.send("You cannot purge more than 100 messages at a time!")
        fi = await self.purged_txt(ctx, message_count)
        try:
            pmsg = await ctx.channel.purge(limit=message_count)
        except Exception as e:
            self.bot.log.error(e)
            return await ctx.send('❌ Cannot purge messages!')

        msg = f'🗑️ **{len(pmsg)} messages purged** in {ctx.channel.mention} | {ctx.channel.name}\n'
        msg += f'Purger was {ctx.author.mention} | {ctx.author}\n'
        if reason:
            msg += f"\N{PENCIL} __Reason__: \"{reason}\""
        else:
            pass
        await self.log_send(ctx, msg, file=fi)

    @commands.guild_only()
    @commands.command(aliases=["nick"])
    @is_staff_or_has_perms("Helper", manage_nicknames=True)
    async def nickname(self, ctx, target: discord.Member, *, nickname: str = ''):
        """Sets a user's nickname.

        In order to use this command, you must either have
        Manage Nicknames permission or a role that
        is assigned as a Helper or above in the bot."""
        try:
            await target.edit(nick=nickname)
        except discord.errors.Forbidden:
            await ctx.send("I can't change their nickname!")
            return

        await ctx.safe_send(f"Successfully changed {target.name}'s nickname.")

    async def get_mute_role(self, ctx):
        """Gets the guild's mute role if it exists"""
        query = """SELECT mute_role_id FROM guild_mod_config
                   WHERE guild_id=$1;
                """
        config = await self.bot.db.fetchval(query, ctx.guild.id)
        if config:
            role = discord.utils.get(ctx.guild.roles, id=config)
            if role:
                return role
            else:
                raise MuteRoleError("The mute role that was configured "
                                    "seems to be deleted! "
                                    "Please setup a new mute role.")
        else:
            raise MuteRoleError("You do not have a mute role setup!")

    @commands.guild_only()
    @commands.command(aliases=['muteuser'])
    @commands.bot_has_permissions(manage_roles=True)
    @is_staff_or_has_perms("Moderator", manage_roles=True)
    async def mute(self, ctx, target: TargetMember, *, reason: str = ""):
        """Mutes a user.

        In order to use this command, you must either have
        Manage Roles permission or a role that
        is assigned as a Moderator or above in the bot."""
        role = await self.get_mute_role(ctx)

        safe_name = await commands.clean_content().convert(ctx, str(target))
        dm_message = f"You were muted on {ctx.guild.name}!"
        opt_reason = "[Mute] "
        if reason:
            dm_message += f" The given reason is: \"{reason}\"."
            opt_reason += f"{reason}"
        try:
            await target.send(dm_message)
        except discord.errors.Forbidden:
            # Prevents issues in cases where user blocked bot
            # or has DMs disabled
            pass

        await target.add_roles(role, reason=f"{self.mod_reason(ctx, opt_reason)}")

        chan_message = f"🔇 **Muted**: {ctx.author.mention} muted "\
                       f"{target.mention} | {safe_name}\n"\
                       f"🏷 __User ID__: {target.id}\n"
        if reason:
            chan_message += f"\N{PENCIL} __Reason__: \"{reason}\""
        else:
            chan_message += f"\nPlease add an explanation below. In the future, "\
                            f"it is recommended to use `{ctx.prefix}mute <user> [reason]`"\
                            f" as the reason is automatically sent to the user."
        await self.set_user_restrictions(ctx.guild.id, target.id, role.id)
        await ctx.send(f"{target.mention} can no longer speak.")
        await self.log_send(ctx, chan_message)

    async def mute_role_check(self, ctx, target, role):
        query = """SELECT * FROM user_restrictions
                WHERE guild_id=$1 AND user_id=$2 AND role_id=$3"""
        return await self.bot.db.fetchval(query, ctx.guild.id, target.id, role.id)

    @commands.guild_only()
    @commands.command()
    @commands.bot_has_permissions(manage_roles=True)
    @is_staff_or_has_perms("Moderator", manage_roles=True)
    async def unmute(self, ctx, target: discord.Member):
        """Unmutes a user.

        In order to use this command, you must either have
        Manage Roles permission or a role that
        is assigned as a Moderator or above in the bot."""
        role = await self.get_mute_role(ctx)
        role_check_2 = await self.mute_role_check(ctx, target, role)
        if role not in target.roles or role_check_2 is None:
            return await ctx.send('This user is not muted!')
        await target.remove_roles(role, reason=f"{self.mod_reason(ctx, '[Unmute]')}")
        safe_name = await commands.clean_content().convert(ctx, str(target))
        chan_message = f"🔈 **Unmuted**: {ctx.author.mention} unmuted "\
                       f"{target.mention} | {safe_name}\n"\
                       f"🏷 __User ID__: {target.id}\n"
        await self.remove_user_restriction(ctx.guild.id, target.id, role.id)
        await ctx.send(f"{target.mention} can now speak again.")
        await self.log_send(ctx, chan_message)

    @commands.guild_only()
    @commands.command()
    @commands.bot_has_permissions(ban_members=True)
    @is_staff_or_has_perms("Moderator", ban_members=True)
    async def unban(self, ctx, user_id: int, *, reason: str = ""):
        """Unbans a user.

        In order to use this command, you must either have
        Ban Members permission or a role that
        is assigned as a Moderator or above in the bot."""
        # A Re-implementation of the BannedMember converter taken from RoboDanny.
        # https://github.com/Rapptz/RoboDanny/blob/rewrite/cogs/mod.py
        ban_list = await ctx.guild.bans()
        try:
            member_id = int(user_id)
            entity = discord.utils.find(lambda u: u.user.id == member_id, ban_list)
        except ValueError:  # We'll fix this soon. It Just Works:tm: for now
            entity = discord.utils.find(lambda u: str(u.user) == user_id, ban_list)

        if entity is None:
            return await ctx.send("❌ Not a valid previously-banned member.")
            # This is a mess :p
        member = await self.bot.fetch_user(user_id)

        await ctx.guild.unban(member, reason=f"{self.mod_reason(ctx, reason)}")

        chan_message = f"⭕ **Unban**: {ctx.author.mention} unbanned "\
                       f"{member.mention} | {member}\n"\
                       f"🏷 __User ID__: {member.id}\n"
        if reason:
            chan_message += f"\N{PENCIL} __Reason__: \"{reason}\""
        else:
            chan_message += f"\nPlease add an explanation below. In the future, "\
                            f"it is recommended to use `{ctx.prefix}unban <user_id> [reason]`."
        await ctx.send(f"{user_id} is now unbanned.")
        await self.log_send(ctx, chan_message)

    @commands.guild_only()
    @commands.command(aliases=['hackban'])
    @commands.bot_has_permissions(ban_members=True)
    @is_staff_or_has_perms("Moderator", ban_members=True)
    async def banid(self, ctx, user_id: int, *, reason: str = ""):
        """Bans a user by ID (hackban).

        In order to use this command, you must either have
        Ban Members permission or a role that
        is assigned as a Moderator or above in the bot."""
        try:
            user = await self.bot.fetch_user(user_id)
        except discord.errors.NotFound:
            await ctx.send(f"❌ No user associated with ID `{user_id}`.")
        target_member = ctx.guild.get_member(user_id)
        # Hedge-proofing the code
        if user == self.bot.user:  # Idiots
            return await ctx.send("You can't do mod actions on me.")
        elif user == ctx.author.id:
            return await ctx.send("You can't do mod actions on yourself.")
        elif target_member and await member_at_least_has_staff_role(self, target_member):
            return await ctx.send("I can't ban this user as "
                                  "they're a staff member.")

        safe_name = await commands.clean_content().convert(ctx, str(user_id))

        await ctx.guild.ban(user,
                            reason=f"{self.mod_reason(ctx, reason)}",
                            delete_message_days=0)
        await ctx.send(f"{user} | {safe_name} is now b&. 👍")

        chan_message = f"⛔ **Hackban**: {ctx.author.mention} banned "\
                       f"{user.mention} | {safe_name}\n"\
                       f"🏷 __User ID__: {user_id}\n"
        if reason:
            chan_message += f"\N{PENCIL} __Reason__: \"{reason}\""
        else:
            chan_message += f"\nPlease add an explanation below. In the future"\
                            f", it is recommended to use "\
                            f"`{ctx.prefix}banid <user> [reason]`."
        await self.log_send(ctx, chan_message)

    @commands.guild_only()
    @commands.bot_has_permissions(ban_members=True)
    @is_staff_or_has_perms("Moderator", ban_members=True)
    @commands.command(aliases=['tempban'])
    async def timeban(self, ctx, target: TargetMember,
                      duration: FutureTime, *, reason: str = ""):
        """Bans a user for a specified amount of time.

        The duration can be a short time format such as "30d",
        a more human duration format such as "until Monday at 7PM",
        or a more concrete time format such as "2020-12-31".

        Note that duration time is in UTC.

        In order to use this command, you must either have
        Ban Members permission or a role that
        is assigned as a Moderator or above in the bot."""
        duration_text = get_utc_timestamp(duration.dt)
        timed_txt = natural_timedelta(duration.dt)
        duration_text = f"{timed_txt} ({duration_text})"
        timer = self.bot.get_cog('TasksManagement')
        if not timer:
            raise TimersUnavailable
        ext = {"guild_id": ctx.guild.id, "user_id": target.id,
               "mod_id": ctx.author.id}
        await timer.add_job("timeban", ctx.message.created_at,
                            duration.dt, ext)

        safe_name = await commands.clean_content().convert(ctx, str(target))

        dm_message = f"You were banned from {ctx.guild.name}."
        if reason:
            dm_message += f" The given reason is: \"{reason}\"."
        dm_message += f"\n\nThis ban will expire in {duration_text}."

        try:
            await target.send(dm_message)
        except discord.errors.Forbidden:
            # Prevents ban issues in cases where user blocked bot
            # or has DMs disabled
            pass
        if reason:
            opt_reason = f"{reason} (Timeban expires in {duration_text})"
        else:
            opt_reason = f" (Timeban expires in {duration_text})"
        await ctx.guild.ban(target, reason=f"{self.mod_reason(ctx, opt_reason)}",
                            delete_message_days=0)
        chan_message = f"⛔ **Timed Ban**: {ctx.author.mention} banned "\
                       f"{target.mention} for {duration_text} | {safe_name}\n"\
                       f"🏷 __User ID__: {target.id}\n"
        if reason:
            chan_message += f"\N{PENCIL} __Reason__: \"{reason}\""
        else:
            chan_message += "\nPlease add an explanation below. In the future"\
                            f", it is recommended to use `{ctx.prefix}timeban"\
                            " <target> <duration> [reason]`"\
                            " as the reason is automatically sent to the user."
        await ctx.send(f"{safe_name} is now b&. "
                       f"It will expire in {duration_text}. 👍")
        await self.log_send(ctx, chan_message)

    @commands.guild_only()
    @commands.command(aliases=['tempmute'])
    @commands.bot_has_permissions(manage_roles=True)
    @is_staff_or_has_perms("Moderator", manage_roles=True)
    async def timemute(self, ctx, target: TargetMember,
                       duration: FutureTime, *, reason: str = ""):
        """Mutes a user for a specified amount of time.

        The duration can be a short time format such as "30d",
        a more human duration format such as "until Monday at 7PM",
        or a more concrete time format such as "2020-12-31".

        Note that duration time is in UTC.

        In order to use this command, you must either have
        Manage Roles permission or a role that
        is assigned as a Moderator or above in the bot."""
        role = await self.get_mute_role(ctx)
        duration_text = get_utc_timestamp(duration.dt)
        timed_txt = natural_timedelta(duration.dt)
        duration_text = f"{timed_txt} ({duration_text})"
        timer = self.bot.get_cog('TasksManagement')
        if not timer:
            raise TimersUnavailable
        ext = {"guild_id": ctx.guild.id, "user_id": target.id,
               "role_id": role.id, "mod_id": ctx.author.id}
        await timer.add_job("timed_restriction", ctx.message.created_at,
                            duration.dt, ext)
        safe_name = await commands.clean_content().convert(ctx, str(target))
        dm_message = f"You were muted on {ctx.guild.name}!"
        if reason:
            dm_message += f" The given reason is: \"{reason}\"."
        dm_message += f"\n\nThis mute will expire in {duration_text}."

        try:
            await target.send(dm_message)
        except discord.errors.Forbidden:
            # Prevents mute issues in cases where user blocked bot
            # or has DMs disabled
            pass
        if reason:
            opt_reason = f"{reason} (Timemute expires in {duration_text})"
        else:
            opt_reason = f" (Timemute expires in {duration_text})"

        await target.add_roles(role, reason=f"{self.mod_reason(ctx, opt_reason)}")

        chan_message = f"🔇 **Timed Mute**: {ctx.author.mention} muted "\
                       f"{target.mention} for {duration_text} | {safe_name}\n"\
                       f"🏷 __User ID__: {target.id}\n"
        if reason:
            chan_message += f"\N{PENCIL} __Reason__: \"{reason}\""
        else:
            chan_message += "\nPlease add an explanation below. In the future, "\
                            f"it is recommended to use `{ctx.prefix}timemute <user> "\
                            "<duration> [reason]`"\
                            " as the reason is automatically sent to the user."
        await self.set_user_restrictions(ctx.guild.id, target.id, role.id)
        await ctx.send(f"{target.mention} can no longer speak. "
                       f"It will expire in {duration_text}.")
        await self.log_send(ctx, chan_message)

    @commands.guild_only()
    @commands.bot_has_permissions(manage_channels=True)
    @is_staff_or_has_perms("Moderator", manage_channels=True)
    @commands.command(aliases=['lockdown'])
    async def lock(self, ctx, channel: discord.TextChannel = None):
        """Locks down the channel mentioned.

        Sets the channel permissions as @everyone can't send messages.

        If no channel was mentioned, it locks the channel the command was used in.

        In order to use this command, You must either have
        Manage Channels permission or a role that
        is assigned as a Moderator or above in the bot."""
        if not channel:
            channel = ctx.channel

        if channel.overwrites_for(ctx.guild.default_role).send_messages is False:
            await ctx.send(f"🔒 {channel.mention} is already locked down. "
                           f"Use `{ctx.prefix}unlock` to unlock.")
            return

        await channel.set_permissions(ctx.guild.default_role, send_messages=False, add_reactions=False)
        await channel.send(f"🔒 {channel.mention} is now locked.")

        # Define Safe Name so we don't mess this up (again)
        safe_name = await commands.clean_content().convert(ctx, str(ctx.author))
        log_message = f"🔒 **Lockdown** in {channel.mention} by {ctx.author.mention} | {safe_name}"
        await self.log_send(ctx, log_message)

    @commands.guild_only()
    @commands.bot_has_permissions(manage_channels=True)
    @is_staff_or_has_perms("Admin", manage_channels=True)
    @commands.command(aliases=['hard-lock'])
    async def hlock(self, ctx, channel: discord.TextChannel = None):
        """Hard locks a channel.

        Sets the channel permissions as @everyone can't speak or see the channel.

        If no channel was mentioned, it hard locks the channel the command was used in.

        In order to use this command, You must either have
        Manage Channels permission or a role that
        is assigned as an Admin or above in the bot."""
        if not channel:
            channel = ctx.channel

        if channel.overwrites_for(ctx.guild.default_role).read_messages is False:
            await ctx.send(f"🔒 {channel.mention} is already hard locked. "
                           f"Use `{ctx.prefix}hard-unlock` to unlock the channel.")
            return

        await channel.set_permissions(ctx.guild.default_role, read_messages=False)
        await channel.send(f"🔒 {channel.mention} is now hard locked.")

        # Define Safe Name so we don't mess this up (again)
        safe_name = await commands.clean_content().convert(ctx, str(ctx.author))
        log_message = f"🔒 **Hard Lockdown** in {channel.mention} "\
                      f"by {ctx.author.mention} | {safe_name}"
        await self.log_send(ctx, log_message)

    @commands.guild_only()
    @commands.bot_has_permissions(manage_channels=True)
    @is_staff_or_has_perms("Moderator", manage_channels=True)
    @commands.command()
    async def unlock(self, ctx, channel: discord.TextChannel = None):
        """Unlocks the channel mentioned.

        If no channel was mentioned, it unlocks the channel the command was used in.

        In order to use this command, You must either have
        Manage Channels permission or a role that
        is assigned as a Moderator or above in the bot."""
        if not channel:
            channel = ctx.channel

        if channel.overwrites_for(ctx.guild.default_role).send_messages is None:
            await ctx.send(f"🔓 {channel.mention} is already unlocked.")
            return

        await channel.set_permissions(ctx.guild.default_role, send_messages=None, add_reactions=None)
        await channel.send(f"🔓 {channel.mention} is now unlocked.")

        # Define Safe Name so we don't mess this up (again)
        safe_name = await commands.clean_content().convert(ctx, str(ctx.author))
        log_message = f"🔓 **Unlock** in {channel.mention} by {ctx.author.mention} | {safe_name}"
        await self.log_send(ctx, log_message)

    @commands.guild_only()
    @commands.bot_has_permissions(manage_channels=True)
    @is_staff_or_has_perms("Admin", manage_channels=True)
    @commands.command(aliases=['hard-unlock'])
    async def hunlock(self, ctx, channel: discord.TextChannel = None):
        """Hard unlocks the channel mentioned.

        If no channel was mentioned, it unlocks the channel the command was used in.

        In order to use this command, You must either have
        Manage Channels permission or a role that
        is assigned as an Admin or above in the bot."""
        if not channel:
            channel = ctx.channel

        if channel.overwrites_for(ctx.guild.default_role).read_messages is None:
            await ctx.send(f"🔓 {channel.mention} is already unlocked.")
            return

        await channel.set_permissions(ctx.guild.default_role, read_messages=None)
        await channel.send(f"🔓 {channel.mention} is now unlocked.")

        # Define Safe Name so we don't mess this up (again)
        safe_name = await commands.clean_content().convert(ctx, str(ctx.author))
        log_message = f"🔓 **Hard Unlock** in {channel.mention} by {ctx.author.mention} | {safe_name}"
        await self.log_send(ctx, log_message)

    @commands.guild_only()
    @commands.bot_has_permissions(manage_messages=True)
    @is_staff_or_has_perms("Moderator", manage_messages=True)
    @commands.command()
    async def pin(self, ctx, message_id: int, channel: discord.TextChannel = None):
        """Pins a message by ID."""
        if not channel:
            channel = ctx.channel
        try:
            msg = await channel.fetch_message(message_id)
        except discord.NotFound:
            return await ctx.send("Message ID not found.")
        try:
            await msg.pin()
        except discord.HTTPException as e:
            return await self.bot.create_error_ticket(ctx, "Error", e)
        await ctx.send("\N{OK HAND SIGN}")

    @commands.guild_only()
    @commands.bot_has_permissions(manage_messages=True)
    @is_staff_or_has_perms("Moderator", manage_messages=True)
    @commands.command()
    async def unpin(self, ctx, message_id: int, channel: discord.TextChannel = None):
        """Unpins a message by ID."""
        if not channel:
            channel = ctx.channel
        try:
            msg = await channel.fetch_message(message_id)
        except discord.NotFound:
            return await ctx.send("Message ID not found.")
        try:
            await msg.unpin()
        except discord.HTTPException as e:
            return await self.bot.create_error_ticket(ctx, "Error", e)
        await ctx.send("\N{OK HAND SIGN}")

    @commands.guild_only()
    @is_staff_or_has_perms("Moderator", manage_messages=True)
    @commands.command()
    async def clean(self, ctx, max_messages: int = 100,
                    channel: discord.TextChannel = None):
        """Cleans the bot's messages from the channel specified.

        If no channel is specified, the bot deletes its
        messages from the channel the command was run in.

        If a max_messages number is specified, it will delete
        that many messages from the bot in the specified channel.

        In order to use this command, you must either have
        Manage Messages permission or a role that
        is assigned as a Moderator or above in the bot.
        """
        if channel is None:
            channel = ctx.channel
        if (max_messages > 100):
            raise commands.BadArgument("Cannot purge more than 100 messages.")
        has_perms = ctx.channel.permissions_for(ctx.guild.me).manage_messages
        await channel.purge(limit=max_messages, check=lambda b: b.author == ctx.bot.user,
                            before=ctx.message.created_at,
                            after=datetime.utcnow() - timedelta(days=14),
                            bulk=has_perms)
        await ctx.send("\N{OK HAND SIGN}", delete_after=15)

    @commands.Cog.listener()
    async def on_timeban_job_complete(self, jobinfo):
        ext = json.loads(jobinfo['extra'])
        guild = self.bot.get_guild(ext['guild_id'])
        if guild is None:
            # Bot was kicked.
            return
        try:
            uid = await self.bot.fetch_user(ext['user_id'])
            msg = f"⚠ **Ban expired**: <@!{ext['user_id']}> | {discord.utils.escape_mentions(str(uid))}"\
                  f"\nTimeban was made by"
        except Exception:
            uid = discord.Object(id=ext['user_id'])
            msg = f"⚠ **Ban expired**: <@!{ext['user_id']}>"\
                  f"\nTimeban was made by"
        moderator = guild.get_member(ext['mod_id'])
        if moderator is None:
            try:
                moderator = await self.bot.fetch_user(ext['mod_id'])
            except Exception:
                # Discord Broke/Failed/etc.
                mod = f"Moderator ID {ext['mod_id']}"
                msg += f" {mod}"
            else:
                mod = f'{moderator} (ID: {moderator.id})'
                msg += f" <@!{moderator}> | {discord.utils.escape_mentions(str(moderator))}"
        else:
            mod = f'{moderator} (ID: {moderator.id})'
            msg += f" {moderator.mention} | {discord.utils.escape_mentions(str(moderator))}"
        reason = f"Timed ban made by {mod} at {jobinfo['created']} expired"
        msg += f" at {get_utc_timestamp(jobinfo['created'])}."
        await guild.unban(uid, reason=reason)
        await self.logid_send(ext['guild_id'], msg)

    @commands.Cog.listener()
    async def on_timed_restriction_job_complete(self, jobinfo):
        ext = json.loads(jobinfo['extra'])
        guild = self.bot.get_guild(ext['guild_id'])
        if guild is None:
            # Bot was kicked.
            return
        moderator = guild.get_member(ext['mod_id'])
        if moderator is None:
            try:
                mod = await self.bot.fetch_user(ext['mod_id'])
            except Exception:
                # Discord Broke/Failed/etc.
                mod = f"Moderator ID {ext['mod_id']}"
            else:
                mod = f'{moderator} (ID: {moderator.id})'
        else:
            mod = f'{moderator} (ID: {moderator.id})'
        role = guild.get_role(ext['role_id'])
        if role is None:
            # Role was deleted or something.
            await self.remove_user_restriction(guild.id,
                                               ext['user_id'],
                                               ext['role_id'])
            return
        user = guild.get_member(ext['user_id'])
        if user is None:
            # User left so we remove the restriction and return.
            await self.remove_user_restriction(guild.id,
                                               ext['user_id'],
                                               ext['role_id'])
            msg = f"⚠ **Timed restriction expired** {ext['user_id']}\n"\
                  f"\N{LABEL} __Role__: {discord.utils.escape_mentions(role.name)} "\
                  f"| {role.id}\n"\
                  f"Timed restriction was made by "\
                  f"{discord.utils.escape_mentions(str(mod))} at "\
                  f"{get_utc_timestamp(jobinfo['created'])}."
            await self.logid_send(ext['guild_id'], msg)
            return
        reason = f"Timed restriction made by {mod} at "\
                 f"{get_utc_timestamp(jobinfo['created'])} expired"
        await self.remove_user_restriction(guild.id,
                                           user.id,
                                           role.id)
        msg = f"⚠ **Timed restriction expired:** {user.mention} | {user.id}\n"\
              f"\N{LABEL} __Role__: {discord.utils.escape_mentions(role.name)} "\
              f"| {role.id}\n"\
              f"Timed restriction was made by "\
              f"{discord.utils.escape_mentions(str(mod))} at "\
              f"{get_utc_timestamp(jobinfo['created'])}."
        await self.logid_send(ext['guild_id'], msg)
        await user.remove_roles(role, reason=reason)

# Most commands here taken from robocop-ngs mod.py
# https://github.com/aveao/robocop-ng/blob/master/cogs/mod_user.py
# robocop-ng is MIT licensed

    async def get_userlog_embed_for_id(self, ctx, uid: str, name: str, guild,
                                       own: bool = False, event=""):
        own_note = " Good for you!" if own else ""
        wanted_events = ["warns", "bans", "kicks", "mutes"]
        if event:
            wanted_events = [event]
        userlog = await get_userlog(self.bot, guild)

        if uid not in userlog:
            embed = discord.Embed(title=f"Warns for {name}")
            embed.description = f"There are none!{own_note} (no entry)"
            embed.color = discord.Color.green()
            return await ctx.send(embed=embed)
        entries = []
        for event_type in wanted_events:
            if event_type in userlog[uid] and userlog[uid][event_type]:
                event_name = userlog_event_types[event_type]
                for idx, event in enumerate(userlog[uid][event_type]):
                    issuer = "" if own else f"Issuer: {event['issuer_name']} " \
                                            f"({event['issuer_id']})\n"
                    entries.append((f"{event_name} {idx + 1}: "
                                    f"{event['timestamp']}",
                                    issuer + f"Reason: {event['reason']}"))
        if len(entries) == 0:
            embed = discord.Embed(title=f"Warns for {name}")
            embed.description = f"There are none!{own_note}"
            embed.color = 0x2ecc71
            return await ctx.send(embed=embed)
        embed = WarnPages(f"Warns for {name}", ctx, entries=entries, per_page=5)
        embed.embed.color = 0x992d22
        return await embed.paginate()

    async def clear_event_from_id(self, uid: str, event_type, guild):
        userlog = await get_userlog(self.bot, guild)
        if uid not in userlog:
            return f"<@{uid}> has no {event_type}!"
        event_count = len(userlog[uid][event_type])
        if not event_count:
            return f"<@{uid}> has no {event_type}!"
        userlog[uid][event_type] = []
        await set_userlog(self.bot, guild, userlog)
        return f"<@{uid}> no longer has any {event_type}!"

    async def delete_event_from_id(self, uid: str, idx: int, event_type, guild):
        userlog = await get_userlog(self.bot, guild)
        if uid not in userlog:
            return f"<@{uid}> has no {event_type}!"
        event_count = len(userlog[uid][event_type])
        if not event_count:
            return f"<@{uid}> has no {event_type}!"
        if idx > event_count:
            return "Index is higher than " \
                   f"count ({event_count})!"
        if idx < 1:
            return "Index is below 1!"
        event = userlog[uid][event_type][idx - 1]
        event_name = userlog_event_types[event_type]
        embed = discord.Embed(color=discord.Color.dark_red(),
                              title=f"{event_name} {idx} on "
                                    f"{event['timestamp']}",
                              description=f"Issuer: {event['issuer_name']}\n"
                                          f"Reason: {event['reason']}")
        del userlog[uid][event_type][idx - 1]
        await set_userlog(self.bot, guild, userlog)
        return embed

    @commands.guild_only()
    @is_staff_or_has_perms("Helper", manage_messages=True)
    @commands.command(name="listwarns")
    async def userlog_cmd(self, ctx, target: discord.Member):
        """Lists warns for a user.

        In order to use this command, You must either have
        Manage Messages permission or a role that
        is assigned as a Helper or above in the bot."""
        await self.get_userlog_embed_for_id(ctx, str(target.id), str(target),
                                            event="warns", guild=ctx.guild)

    @commands.guild_only()
    @commands.command()
    async def mywarns(self, ctx):
        """Lists your warns."""
        await self.get_userlog_embed_for_id(ctx, str(ctx.author.id),
                                            str(ctx.author),
                                            own=True,
                                            event="warns",
                                            guild=ctx.guild)

    @commands.guild_only()
    @is_staff_or_has_perms("Helper", manage_messages=True)
    @commands.command()
    async def listwarnsid(self, ctx, target: int):
        """Lists all the warns for a user by ID.

        In order to use this command, You must either have
        Manage Messages permission or a role that
        is assigned as a Helper or above in the bot."""
        await self.get_userlog_embed_for_id(ctx, str(target), str(target),
                                            event="warns", guild=ctx.guild)

    @commands.guild_only()
    @is_staff_or_has_perms("Admin", administrator=True)
    @commands.command()
    async def clearwarns(self, ctx, target: discord.Member):
        """Clears all warns for a user.

        In order to use this command, You must either have
        Administrator permission or a role that
        is assigned as an Admin or above in the bot."""
        msg = await self.clear_event_from_id(str(target.id), "warns", guild=ctx.guild)
        await ctx.send(msg)
        safe_name = await commands.clean_content().convert(ctx, str(target))
        msg = f"🗑 **Cleared warns**: {ctx.author.mention} cleared" \
              f" all warns of {target.mention} | " \
              f"{safe_name}"
        await self.log_send(ctx, msg)

    @commands.guild_only()
    @is_staff_or_has_perms("Admin", administrator=True)
    @commands.command()
    async def clearwarnsid(self, ctx, target: int):
        """Clears all warns for a userid.

        In order to use this command, You must either have
        Administrator permission or a role that
        is assigned as an Admin or above in the bot."""
        msg = await self.clear_event_from_id(str(target), "warns", guild=ctx.guild)
        await ctx.send(msg)
        msg = f"🗑 **Cleared warns**: {ctx.author.mention} cleared" \
              f" all warns of <@{target}> "
        await self.log_send(ctx, msg)

    @commands.guild_only()
    @is_staff_or_has_perms("Admin", administrator=True)
    @commands.command(aliases=["deletewarn"])
    async def delwarn(self, ctx, target: discord.Member, idx: int):
        """Removes a specific warn from a user.

        In order to use this command, You must either have
        Administrator permission or a role that
        is assigned as an Admin or above in the bot."""
        del_event = await self.delete_event_from_id(str(target.id),
                                                    idx, "warns",
                                                    guild=ctx.guild)
        event_name = "warn"
        # This is hell.
        if isinstance(del_event, discord.Embed):
            await ctx.send(f"{target.mention} has a {event_name} removed!")
            safe_name = await commands.clean_content().convert(ctx, str(target))
            msg = f"🗑 **Deleted {event_name}**: " \
                  f"{ctx.author.mention} removed " \
                  f"{event_name} {idx} from {target.mention} | " \
                  f"{safe_name}"
            await self.log_send(ctx, msg, embed=del_event)
        else:
            await ctx.send(del_event)

    @commands.guild_only()
    @is_staff_or_has_perms("Admin", administrator=True)
    @commands.command(aliases=["deletewarnid"])
    async def delwarnid(self, ctx, target: int, idx: int):
        """Removes a specific warn from a userid.

        In order to use this command, You must either have
        Administrator permission or a role that
        is assigned as an Admin or above in the bot."""
        del_event = await self.delete_event_from_id(str(target),
                                                    idx, "warns",
                                                    guild=ctx.guild)
        event_name = "warn"
        # This is hell.
        if isinstance(del_event, discord.Embed):
            await ctx.send(f"<@{target}> has a {event_name} removed!")
            msg = f"🗑 **Deleted {event_name}**: " \
                  f"{ctx.author.mention} removed " \
                  f"{event_name} {idx} from <@{target}> "
            await self.log_send(ctx, msg, embed=del_event)
        else:
            await ctx.send(del_event)


def setup(bot):
    bot.add_cog(Mod(bot))
