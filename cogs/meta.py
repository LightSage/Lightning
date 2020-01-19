# Lightning.py - A multi-purpose Discord bot
# Copyright (C) 2020 - LightSage
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

import asyncio
import collections
import inspect
import itertools
import json
import os
import time
import traceback
from datetime import datetime
from typing import Union

import discord
from discord.ext import commands, tasks, flags

import resources.botemojis as emoji
from utils.checks import is_bot_manager
from utils.converters import ReadableChannel
from utils.errors import ChannelPermissionFailure, MessageNotFoundInChannel
from utils.paginator import Pages, TextPages
from utils.time import natural_timedelta, get_relative_timestamp


class NonGuildUser(commands.Converter):
    async def convert(self, ctx, argument):
        if argument.isdigit() is False:
            raise commands.BadArgument("Not a valid user ID!")
        try:
            return await ctx.bot.fetch_user(argument)
        except discord.NotFound:
            raise commands.BadArgument("Not a valid user ID!")
        except discord.HTTPException:
            raise commands.BadArgument('Error occurred while finding the user!')

# Paginated Help Command taken from https://github.com/Rapptz/RoboDanny/blob/rewrite/cogs/meta.py
# MIT Licensed - Copyright (c) 2015 Rapptz
# https://github.com/Rapptz/RoboDanny/blob/rewrite/LICENSE.txt


class HelpPaginator(Pages):
    def __init__(self, help_command, ctx, entries, *, per_page=4):
        super().__init__(ctx, entries=entries, per_page=per_page)
        self.reaction_emojis.append(('\N{WHITE QUESTION MARK ORNAMENT}', self.show_bot_help))
        self.total = len(entries)
        self.help_command = help_command
        self.prefix = help_command.clean_prefix
        self.is_bot = False

    def get_bot_page(self, page):
        cog, description, commands = self.entries[page - 1]
        self.title = f'{cog} Commands'
        self.description = description
        return commands

    def prepare_embed(self, entries, page, *, first=False):
        self.embed.clear_fields()
        self.embed.description = self.description
        self.embed.title = self.title

        # if self.is_bot:
        #    value ='For more help, join the official bot support server: https://discord.gg/cDPGuYd'
        #    self.embed.add_field(name='Support', value=value, inline=False)

        self.embed.set_footer(text=f'Use "{self.prefix}help command" for more info on a command.')

        for entry in entries:
            signature = f'{entry.qualified_name} {entry.signature}'
            self.embed.add_field(name=signature, value=entry.short_doc or "No help given", inline=False)

        if self.maximum_pages:
            self.embed.set_author(name=f'Page {page}/{self.maximum_pages} ({self.total} commands)')

    async def show_help(self):
        """shows this message"""

        self.embed.title = 'Paginator help'
        self.embed.description = 'Hello! Welcome to the help page.'

        messages = [f'{emoji} {func.__doc__}' for emoji, func in self.reaction_emojis]
        self.embed.clear_fields()
        self.embed.add_field(name='What are these reactions for?', value='\n'.join(messages), inline=False)
        self.embed.add_field(name='Support Server', value="https://discord.gg/cDPGuYd", inline=False)

        self.embed.set_footer(text=f'We were on page {self.current_page} before this message.')
        await self.message.edit(embed=self.embed)

        async def go_back_to_current_page():
            await asyncio.sleep(30.0)
            await self.show_current_page()

        self.bot.loop.create_task(go_back_to_current_page())

    async def show_bot_help(self):
        """shows how to use the bot"""

        self.embed.title = 'Using the bot'
        self.embed.description = 'Hello! Welcome to the help page.'
        self.embed.clear_fields()

        entries = (
            ('<argument>', 'This means the argument is __**required**__.'),
            ('[argument]', 'This means the argument is __**optional**__.'),
            ('[A|B]', 'This means the it can be __**either A or B**__.'),
            ('[argument...]', 'This means you can have multiple arguments.\n'
                              'Now that you know the basics, it should be noted that...\n'
                              '__**You do not type in the brackets!**__')
        )

        self.embed.add_field(name='How do I use this bot?',
                             value='Reading the bot signature is pretty simple.')

        for name, value in entries:
            self.embed.add_field(name=name, value=value, inline=False)

        self.embed.set_footer(text=f'We were on page {self.current_page} before this message.')
        await self.message.edit(embed=self.embed)

        async def go_back_to_current_page():
            await asyncio.sleep(30.0)
            await self.show_current_page()

        self.bot.loop.create_task(go_back_to_current_page())


class PaginatedHelpCommand(commands.HelpCommand):
    def __init__(self):
        super().__init__(command_attrs={
            'cooldown': commands.Cooldown(1, 3.0, commands.BucketType.member),
            'help': 'Shows help about the bot, a command, or a category'
        })

    async def on_help_command_error(self, ctx, error):
        if isinstance(error, commands.CommandInvokeError):
            await ctx.send(str(error.original))

    def get_command_signature(self, command):
        parent = command.full_parent_name
        if len(command.aliases) > 0:
            aliases = '|'.join(command.aliases)
            fmt = f'[{command.name}|{aliases}]'
            if parent:
                fmt = f'{parent} {fmt}'
            alias = fmt
        else:
            alias = command.name if not parent else f'{parent} {command.name}'
        return f'{alias}'

    async def send_bot_help(self, mapping):
        def key(c):
            return c.cog_name or '\u200bNo Category'

        bot = self.context.bot
        entries = await self.filter_commands(bot.commands, sort=True, key=key)
        nested_pages = []
        per_page = 9
        total = 0

        for cog, commands in itertools.groupby(entries, key=key):
            commands = sorted(commands, key=lambda c: c.name)
            if len(commands) == 0:
                continue

            total += len(commands)
            actual_cog = bot.get_cog(cog)
            # get the description if it exists (and the cog is valid) or return Empty embed.
            description = (actual_cog and actual_cog.description) or discord.Embed.Empty
            nested_pages.extend((cog, description, commands[i:i + per_page]) for i in range(0, len(commands), per_page))

        # a value of 1 forces the pagination session
        pages = HelpPaginator(self, self.context, nested_pages, per_page=1)

        # swap the get_page implementation to work with our nested pages.
        pages.get_page = pages.get_bot_page
        pages.is_bot = True
        pages.total = total
        # await self.context.release()
        await pages.paginate()

    async def send_cog_help(self, cog):
        entries = await self.filter_commands(cog.get_commands(), sort=True)
        pages = HelpPaginator(self, self.context, entries)
        pages.title = f'{cog.qualified_name} Commands'
        pages.description = cog.description
        await pages.paginate()

    def common_command_formatting(self, page_or_embed, command):
        page_or_embed.title = self.get_command_signature(command)
        if command.signature:
            usage = f"**Usage**: {command.qualified_name} {command.signature}\n\n"
        else:
            usage = f"**Usage**: {command.qualified_name}\n\n"
        if command.description:
            page_or_embed.description = f'{usage}{command.description}\n\n{command.help}'
        else:
            page_or_embed.description = f'{usage}{command.help}' or 'No help found...'

    async def send_command_help(self, command):
        # No pagination necessary for a single command.
        embed = discord.Embed(colour=discord.Colour(0xf74b06))
        self.common_command_formatting(embed, command)
        await self.context.send(embed=embed)

    async def send_group_help(self, group):
        subcommands = group.commands
        if len(subcommands) == 0:
            return await self.send_command_help(group)

        entries = await self.filter_commands(subcommands, sort=True)
        pages = HelpPaginator(self, self.context, entries)
        self.common_command_formatting(pages, group)

        await pages.paginate()


class Meta(commands.Cog):
    """Commands related to Discord or the bot"""
    def __init__(self, bot):
        self.bot = bot
        self.original_help_command = bot.help_command
        bot.help_command = PaginatedHelpCommand()
        bot.help_command.cog = self
        self.number_places = (
            '\N{FIRST PLACE MEDAL}',
            '\N{SECOND PLACE MEDAL}',
            '\N{THIRD PLACE MEDAL}',
            '4\N{combining enclosing keycap}',
            '5\N{combining enclosing keycap}',
            '6\N{combining enclosing keycap}',
            '7\N{combining enclosing keycap}',
            '8\N{combining enclosing keycap}',
            '9\N{combining enclosing keycap}',
            '\N{KEYCAP TEN}')
        self.bulk_command_insertion.start()
        # Protect our data
        self.dump_lock = asyncio.Lock(loop=bot.loop)
        self.data_todump = []
        self.unavailable_guilds = []
        self.bot.create_error_ticket = self.create_error_ticket

    def cog_unload(self):
        self.bot.help_command = self.original_help_command
        self.bulk_command_insertion.stop()

    async def create_error_ticket(self, ctx, title, information):
        if await ctx.bot.is_owner(ctx.author):
            error = information
            exc = traceback.format_exception(type(error), error, error.__traceback__)
            em = discord.Embed(title="Exception",
                               description=f"```py\n{''.join(exc)}```")
            em.set_footer(text=ctx.command.qualified_name)
            return await ctx.send(embed=em)

        query = """INSERT INTO bug_tickets (status, ticket_info, created)
                   VALUES ($1, $2, $3)
                   RETURNING id;
                """
        ext = {"text": str(information), "author_id": ctx.author.id}
        async with self.bot.db.acquire() as con:
            id = await con.fetchrow(query, "Received", json.dumps(ext), datetime.utcnow())
        e = discord.Embed(title=f"{title} Report - ID: {id[0]}", description=str(information))
        e.set_author(name=ctx.author, icon_url=ctx.author.avatar_url)
        e.timestamp = datetime.utcnow()
        e.set_footer(text="Status: Received")
        ch = self.bot.get_channel(self.bot.config['logging']['bug_reports_channnel'])
        msg = await ch.send(embed=e)
        query = """UPDATE bug_tickets
                   SET guild_id=$2, channel_id=$3, message_id=$4
                   WHERE id=$1;
                """
        async with self.bot.db.acquire() as con:
            await con.execute(query, id[0], msg.guild.id, msg.channel.id, msg.id)
        msg = f"```py\n{str(information)}```\nCreated a ticket with ID {id[0]}. "\
              "You can see updates on your ticket by joining "\
              "the [support server](https://discord.gg/cDPGuYd) and looking in the "\
              f"reports channel."
        embed = discord.Embed(title="Uh oh, my powers overloaded.", description=msg)
        embed.set_footer(text="My developers have been notified about this.")
        await ctx.send(embed=embed)

    @commands.command()
    async def avatar(self, ctx, *, member: Union[discord.Member, NonGuildUser] = None):
        """Displays a user's avatar."""
        if member is None:
            member = ctx.author
        embed = discord.Embed(color=discord.Color.blue(),
                              description=f"[Link to Avatar]({member.avatar_url_as(static_format='png')})")
        embed.set_author(name=f"{member.name}\'s Avatar")
        embed.set_image(url=member.avatar_url)
        await ctx.send(embed=embed)

    @commands.command(aliases=['ui', 'whoami'])
    async def userinfo(self, ctx, *, member: Union[discord.Member, NonGuildUser] = None):
        """Gives info for a user."""
        if member is None:
            member = ctx.author
        if not isinstance(member, discord.Member):
            embed = discord.Embed(title=f'User Info. for {member}')  # , color=member.colour)
            embed.set_thumbnail(url=f'{member.avatar_url}')
            if member.bot:
                embed.description = "This user is a bot."
            var = member.created_at.strftime("%Y-%m-%d %H:%M")
            vale = f"{var} UTC ({natural_timedelta(member.created_at, accuracy=3)})\n"\
                   f"Relative Date: {get_relative_timestamp(time_to=member.created_at)}"
            embed.add_field(name="Account Created On", value=vale)
            embed.set_footer(text='This member is not in this server.')
            return await ctx.send(embed=embed)
        embed = discord.Embed(title=f'User Info. for {member}', color=member.colour)
        embed.set_thumbnail(url=f'{member.avatar_url}')
        if member.bot:
            embed.description = "This user is a bot."
        var = member.created_at.strftime("%Y-%m-%d %H:%M")
        embed.add_field(name="Account Created On", value=f"{var} UTC "
                        f"({natural_timedelta(member.created_at, accuracy=3)})\n"
                        f"Relative Date: {get_relative_timestamp(time_to=member.created_at)}",
                        inline=False)
        statuses = {"dnd": f"{emoji.do_not_disturb} Do Not Disturb",
                    "online": f"{emoji.online} Online",
                    "offline": f"{emoji.offline} Offline",
                    "idle": f"{emoji.idle} Idle"}
        status_text = str(member.status)
        status_text = statuses[status_text] if status_text in statuses else status_text
        embed.add_field(name='Status', value=status_text, inline=True)
        activity = getattr(member, 'activity', None)
        if activity is not None:
            if isinstance(member.activity, discord.Spotify):
                artists = ', '.join(member.activity.artists)
                spotifyact = f"Listening to [{member.activity.title}]"\
                             f"(https://open.spotify.com/track/{member.activity.track_id})"\
                             f" by {artists}"
                embed.add_field(name="Activity", value=spotifyact, inline=False)
            elif isinstance(member.activity, discord.Streaming):
                embed.add_field(name="Activity", value=f"Streaming [{member.activity.name}]"
                                                       f"({member.activity.url})", inline=False)
            elif isinstance(member.activity, discord.CustomActivity):
                if member.activity.emoji.animated is False:
                    ret = ".png"
                else:
                    ret = ".gif"
                cdn = f'https://cdn.discordapp.com/emojis/{member.activity.emoji.id}{ret}'
                activity = f"[{str(member.activity.emoji)}]({cdn}) {member.activity.name}"
                embed.add_field(name="Activity", value=activity, inline=False)
            else:
                embed.add_field(name="Activity", value=member.activity.name, inline=False)
        joined_at = getattr(member, 'joined_at', None)
        if joined_at is not None:
            joined = member.joined_at.strftime('%Y-%m-%d %H:%M UTC')
            embed.add_field(name="Joined", value=f"{joined} "
                            f"({natural_timedelta(member.joined_at, accuracy=3)})\n"
                            f"Relative Date: {get_relative_timestamp(time_to=member.joined_at)}",
                            inline=False)
        else:
            embed.add_field(name="Joined", value="N/A", inline=False)
        if hasattr(member, 'roles'):
            roles = [x.mention for x in member.roles]
            if ctx.guild.default_role.mention in roles:
                roles.remove(ctx.guild.default_role.mention)
            if roles:
                embed.add_field(name=f"Roles [{len(roles)}]",
                                value=", ".join(roles) if len(roles) < 10 else "Cannot show all roles",
                                inline=False)
        embed.set_footer(text=f'User ID: {member.id}')
        await ctx.send(embed=embed)

    @userinfo.error
    @avatar.error
    async def userinfo_error(self, ctx, error):
        if isinstance(error, commands.BadUnionArgument):
            return await ctx.send("Error finding that user.")

    @commands.command()
    @commands.guild_only()
    async def roleinfo(self, ctx, *, role: discord.Role):
        """Gives information for a role"""
        em = discord.Embed(title=f"Info for {role.name}")
        em.color = role.color if role.color.value != 0 else em.Empty
        em.add_field(name="Creation", value=natural_timedelta(role.created_at, accuracy=3))
        # Permissions
        allowed = []
        for name, value in role.permissions:
            name = name.replace('_', ' ').replace('guild', 'server').title()
            if value:
                allowed.append(name)
        em.add_field(name="Permissions",
                     value=f"Value: {role.permissions.value}\n\n" + ", ".join(allowed),
                     inline=False)
        em.add_field(name="Role Members", value=len(role.members))
        if role.managed:
            em.description = ("This role is managed by an integration of some sort.")
        await ctx.send(embed=em)

    @flags.add_flag("--simple", "-s", action="store_true")
    @flags.add_flag("--version", "-v", action="store_true")
    @flags.command(name="about", aliases=['info'], usage="[flags]")
    async def about_bot(self, ctx, **flags):
        """Gives information about the bot.

        Flag options (No arguments):
        `--simple`, `-s`: Gives a simple message about the bot.
        `--version`, `-v`: Gives the version that the bot is currently on."""
        if flags['simple']:
            bot_owner = self.bot.get_user(self.bot.owner_id)
            await ctx.send(f"Hi! I'm {str(self.bot.user)}. "
                           "For information on how to invite me, use the "
                           f"botinvite command. My owner is {str(bot_owner)}."
                           " You can find them here: <https://discord.gg/cDPGuYd>.")
            return
        if flags['version']:
            return await ctx.send("I'm currently on "
                                  f"{self.bot.version}!")
        await self.more_about(ctx)

    async def more_about(self, ctx):
        """Gives more information about the bot than the standard about command."""
        query = """SELECT COUNT(*)
                   FROM commands_usage;"""
        amount = await self.bot.db.fetchval(query)
        # Member Stats
        membertotal = 0
        membertotal_online = 0
        for member in self.bot.get_all_members():
            membertotal += 1
            if member.status is not discord.Status.offline:
                membertotal_online += 1
        all_members = f"Total: {membertotal}\n"\
                      f"Unique: {len(self.bot.users)}\n"\
                      f"Unique Members Online: {membertotal_online}"
        embed = discord.Embed(title="Lightning", color=0xf74b06)
        bot_owner = self.bot.get_user(self.bot.owner_id)
        if not bot_owner:
            bot_owner = await self.bot.fetch_user(376012343777427457)
        embed.set_author(name=str(bot_owner), icon_url=bot_owner.avatar_url_as(static_format='png'))
        embed.url = "https://gitlab.com/lightning-bot/Lightning"
        embed.set_thumbnail(url=ctx.me.avatar_url)
        if self.bot.config['bot']['description']:
            embed.description = self.bot.config['bot']['description']
        embed.add_field(name="Servers", value=len(self.bot.guilds))
        embed.add_field(name="Members", value=all_members)
        embed.add_field(name="Command Stats", value=f"{amount} commands used all time.")
        embed.add_field(name="Links", value="[Support Server]"
                                            "(https://discord.gg/cDPGuYd) | "
                                            "[Website](https://lightning-bot.gitlab.io) | "
                                            "[Discord Bots Link]"
                                            "(https://discord.bots.gg/bots/532220480577470464)",
                                            inline=False)
        embed.set_footer(text=f"Lightning {self.bot.version} | Made with "
                              f"discord.py {discord.__version__}")
        await ctx.send(embed=embed)

    @flags.add_flag("--guild", "--server", type=int)
    @flags.command(aliases=['invite', 'join'], usage="[flags]")
    async def botinvite(self, ctx, **flags):
        """Gives you a link to add Lightning to your server.

        Flag options:
        `--guild` or `--server`: Server ID to specify the invite for."""
        perms = discord.Permissions.none()
        perms.kick_members = True
        perms.ban_members = True
        perms.manage_channels = True
        perms.add_reactions = True
        perms.view_audit_log = True
        perms.attach_files = True
        perms.manage_messages = True
        perms.external_emojis = True
        perms.manage_nicknames = True
        perms.manage_emojis = True
        perms.manage_roles = True
        perms.read_messages = True
        perms.send_messages = True
        perms.read_message_history = True
        perms.manage_webhooks = True
        perms.embed_links = True
        if flags['guild']:
            guild = discord.Object(id=flags['guild'])
            invite_link = discord.utils.oauth_url('532220480577470464', perms, guild=guild)
        else:
            invite_link = discord.utils.oauth_url('532220480577470464', perms)
        await ctx.send("You can use this link to invite me to your server. "
                       "(Select permissions as needed) "
                       f"<{invite_link}>")

    @commands.command()
    async def support(self, ctx):
        """Sends an invite that goes to the support server"""
        try:
            await ctx.author.send("Official Support Server Invite: https://discord.gg/cDPGuYd")
            await ctx.message.add_reaction("📬")
        except discord.Forbidden:
            await ctx.send("Official Support Server Invite: https://discord.gg/cDPGuYd")

    @commands.command()
    async def source(self, ctx, *, command: str = None):
        """Gives a link to the source code for a command."""
        source = "https://gitlab.com/lightning-bot/Lightning"
        if command is None:
            return await ctx.send(source)
        if command == "help":
            src = type(self.bot.help_command)
            module = src.__module__
            filename = inspect.getsourcefile(src)
        else:
            obj = self.bot.get_command(command.replace(".", " "))
            if obj is None:
                return await ctx.send("I could not find that command.")
            src = obj.callback.__code__
            module = obj.callback.__module__
            filename = src.co_filename
        lines, firstlineno = inspect.getsourcelines(src)
        location = ""
        if not module.startswith("discord"):
            location = os.path.relpath(filename).replace("\\", "/")
        await ctx.send(f"<{source}/blob/master/{location}#L{firstlineno}"
                       f"-{firstlineno + len(lines) - 1}>")

    @commands.command(hidden=True)
    async def socketstats(self, ctx):
        delta = datetime.utcnow() - self.bot.launch_time
        minutes = delta.total_seconds() / 60
        total = sum(self.bot.socket_stats.values())
        cpm = round(total / minutes)
        events = "\n".join([f"{x}: {y}" for x, y in self.bot.socket_stats.items()])
        await ctx.send(f"{total} socket events observed ({cpm}/minute) ```prolog\n{events}```")

    async def channel_permissions_user(self, channel, member, ctx):
        perms = channel.permissions_for(member)
        em = discord.Embed(title="Channel Permissions", color=member.color)
        allowed = []
        denied = []
        for name, value in perms:
            name = name.replace('_', ' ').replace('guild', 'server').title()
            if value:
                allowed.append(name)
            else:
                denied.append(name)
        if allowed:
            em.add_field(name='Allowed', value='\n'.join(allowed))
        if denied:
            em.add_field(name='Denied', value='\n'.join(denied))
        await ctx.send(embed=em)

    @commands.command()
    @commands.guild_only()
    async def permissions(self, ctx, member: discord.Member = None,
                          channel: discord.TextChannel = None):
        if member is None:
            member = ctx.author
        if channel is None:
            channel = ctx.channel
        await self.channel_permissions_user(channel, member, ctx)

    @commands.command()
    async def ping(self, ctx):
        """Calculates the ping time."""
        before = time.monotonic()
        tmpmsg = await ctx.send('Calculating...')
        after = time.monotonic()
        latencyms = round(self.bot.latency * 1000)
        rtt_ms = round((after - before) * 1000)
        msg = f"🏓 Ping:\nrtt: `{rtt_ms} ms` | gw: `{latencyms} ms`"
        await tmpmsg.edit(content=msg)

    @commands.command()
    async def uptime(self, ctx):
        """Displays my uptime"""
        times = natural_timedelta(self.bot.launch_time, accuracy=None, suffix=False)
        await ctx.send(f"Uptime: {times} "
                       "<:meowbox:563009533530734592>")

    @commands.guild_only()
    @commands.command(aliases=['server', 'guildinfo'])
    async def serverinfo(self, ctx):
        """Shows information about the server"""
        guild = ctx.guild
        embed = discord.Embed(title=f"Server Info for {guild.name}")
        embed.add_field(name='Owner', value=f"{guild.owner.mention} ({guild.owner})")
        embed.add_field(name="Server ID", value=guild.id)
        if guild.icon:
            embed.set_thumbnail(url=guild.icon_url)
        tmp = guild.created_at.strftime("%Y-%m-%d %H:%M")
        embed.add_field(name="Creation", value=f"{tmp} UTC "
                        f"({natural_timedelta(guild.created_at, accuracy=3)})\n"
                        f"Relative Date: {get_relative_timestamp(time_to=guild.created_at)}")
        member_by_status = collections.Counter()
        for m in guild.members:
            member_by_status[str(m.status)] += 1
            if m.bot:
                member_by_status["bots"] += 1
        # Little snippet taken from R. Danny. Under the MIT License
        sta = f'<:online:572962188114001921> {member_by_status["online"]} ' \
              f'<:idle:572962188201820200> {member_by_status["idle"]} ' \
              f'<:dnd:572962188134842389> {member_by_status["dnd"]} ' \
              f'<:offline:572962188008882178> {member_by_status["offline"]} ' \
              f'<:bot_tag:596576775555776522> {member_by_status["bots"]}\n\n'\
              f'Total: {guild.member_count}'

        embed.add_field(name="Members", value=sta)
        static = 0
        animated = 0
        for x, y in enumerate(guild.emojis):
            if y.animated:
                animated += 1
            else:
                static += 1
        emojicalc = f"Static Emotes: {static}\nAnimated Emotes: {animated}"\
                    f"\nTotal: {len(guild.emojis)}"
        embed.add_field(name="Emoji Count", value=emojicalc)

        # Verification Level stuff
        vlevel_replace = {"low": "Low: Member must have a verified email on "
                                 "their Discord account.",
                          "medium": "Medium: Member must have a verified email "
                                    "and be registered on Discord for more than "
                                    "five minutes.",
                          "high": "High (Table Flip): Member must have a verified email, "
                                  "be registered on Discord for more than "
                                  "five minutes, and be a member of the guild "
                                  "itself for more than ten minutes.",
                          "extreme": "Extreme (Double Table Flip): Member must "
                                     "have a verified phone on their Discord account."}
        v_raw_text = str(guild.verification_level)
        verification_text = vlevel_replace[v_raw_text] if v_raw_text in vlevel_replace else v_raw_text
        if verification_text:
            embed.add_field(name="Verification Level", value=verification_text, inline=False)
        if guild.premium_subscription_count:
            boosts = f"Tier: {guild.premium_tier}\n"\
                     f"{guild.premium_subscription_count} boosts."
            embed.add_field(name="Nitro Server Boost", value=boosts)
        await ctx.send(embed=embed)

    @commands.command()
    @commands.guild_only()
    async def memberfind(self, ctx, *, name):
        """Looks for a member that matches the name in the guild"""
        ls = list(filter(lambda m: f"{name}" in m.name.lower(), ctx.guild.members))
        msg = f"**{len(ls)} Results for {name}**:\n"
        for x in ls:
            msg += f"\N{BULLET} {str(x)}\n"
        await ctx.safe_send(msg)

    async def commands_status_guild(self, ctx):
        em = discord.Embed(title=f"Command Stats for {ctx.guild.name}", color=0xf74b06)
        # psql is nice for queries like this. :)
        query = """SELECT COUNT(*), MIN(used_at)
                   FROM commands_usage
                   WHERE guild_id=$1;"""
        res = await self.bot.db.fetchrow(query, ctx.guild.id)
        em.description = f"{res[0]} commands used so far."
        # Default to utcnow() if no value
        em.set_footer(text=f'Lightning has been tracking '
                           'command usage since')
        em.timestamp = res[1] or datetime.utcnow()
        query2 = """SELECT command_name,
                        COUNT(*) as "cmd_uses"
                   FROM commands_usage
                   WHERE guild_id=$1
                   GROUP BY command_name
                   ORDER BY "cmd_uses" DESC
                   LIMIT 5;
                """
        cmds = await self.bot.db.fetch(query2, ctx.guild.id)
        commands_used_des = '\n'.join(f'{self.number_places[index]}: {command_name} (has been used {cmd_uses} times)'
                                      for (index, (command_name, cmd_uses)) in enumerate(cmds))
        if len(commands_used_des) == 0:
            commands_used_des = 'No Commands Used Yet!'
        em.add_field(name="Top Commands Used", value=commands_used_des)
        # Limit 5 commands as I don't want to hit the max on embed field
        # (and also make it look ugly)
        query = """SELECT command_name,
                        COUNT(*) as "cmd_uses"
                   FROM commands_usage
                   WHERE guild_id=$1
                   AND used_at > (timezone('UTC', now()) - INTERVAL '1 day')
                   GROUP BY command_name
                   ORDER BY "cmd_uses" DESC
                   LIMIT 5;
                """
        fetched = await self.bot.db.fetch(query, ctx.guild.id)
        # Shoutouts to R.Danny for this code
        commands_used_des = '\n'.join(f'{self.number_places[index]}: {command_name} (has been used {cmd_uses} times)'
                                      for (index, (command_name, cmd_uses)) in enumerate(fetched))
        if len(commands_used_des) == 0:
            commands_used_des = 'No Commands used yet for today!'
        em.add_field(name="Top Commands Used Today", value=commands_used_des, inline=False)
        if ctx.guild.icon:
            em.set_thumbnail(url=ctx.guild.icon_url)
        await ctx.send(embed=em)
    # Based off of R.Danny

    async def command_status_member(self, ctx, member):
        em = discord.Embed(title=f"Command Stats for {member}", color=0xf74b06)
        # psql is nice for queries like this. :)
        query = "SELECT COUNT(*), MIN(used_at) FROM commands_usage WHERE guild_id=$1 AND user_id=$2;"
        async with self.bot.db.acquire() as con:
            res = await con.fetchrow(query, ctx.guild.id, member.id)
        em.description = f"{res[0]} commands used so far in {ctx.guild.name}."
        # Default to utcnow() if no value
        em.set_footer(text=f'First command usage on')
        em.timestamp = res[1] or datetime.utcnow()
        query2 = """SELECT command_name,
                        COUNT(*) as "cmd_uses"
                   FROM commands_usage
                   WHERE guild_id=$1
                   AND user_id=$2
                   GROUP BY command_name
                   ORDER BY "cmd_uses" DESC
                   LIMIT 10;
                """
        async with self.bot.db.acquire() as con:
            cmds = await con.fetch(query2, ctx.guild.id, member.id)
        commands_used_des = '\n'.join(f'{self.number_places[index]}: {command_name} (has been used {cmd_uses} times)'
                                      for (index, (command_name, cmd_uses)) in enumerate(cmds))
        if len(commands_used_des) == 0:
            commands_used_des = 'No Commands Used Yet!'
        em.add_field(name="Top Commands Used", value=commands_used_des)
        query = """SELECT command_name,
                        COUNT(*) as "cmd_uses"
                   FROM commands_usage
                   WHERE guild_id=$1
                   AND used_at > (timezone('UTC', now()) - INTERVAL '1 day')
                   AND user_id=$2
                   GROUP BY command_name
                   ORDER BY "cmd_uses" DESC
                   LIMIT 5;
                """
        fetched = await self.bot.db.fetch(query, ctx.guild.id, member.id)
        # Shoutouts to R.Danny for this code.
        commands_used_des = '\n'.join(f'{self.number_places[index]}: {command_name} (has been used {cmd_uses} times)'
                                      for (index, (command_name, cmd_uses)) in enumerate(fetched))
        if len(commands_used_des) == 0:
            commands_used_des = 'No Commands used yet for today!'
        em.add_field(name="Top Commands Used Today", value=commands_used_des, inline=False)
        em.set_thumbnail(url=member.avatar_url)
        await ctx.send(embed=em)

    @commands.group(invoke_without_command=True)
    @commands.guild_only()
    async def stats(self, ctx, member: discord.Member = None):
        """Sends stats about which commands are used often in the guild"""
        async with ctx.typing():
            if member is None:
                await self.commands_status_guild(ctx)
            else:
                await self.command_status_member(ctx, member)

    @stats.command(name="all")
    @commands.check(is_bot_manager)
    async def stats_all(self, ctx):
        """Sends stats on the most popular commands used in the bot"""
        async with ctx.typing():
            query = """SELECT command_name,
                        COUNT (*) as "cmd_uses"
                       FROM commands_usage
                       GROUP BY command_name
                       ORDER BY "cmd_uses" DESC
                       LIMIT 10;
                    """
            async with self.bot.db.acquire() as con:
                fetched = await con.fetch(query)
                # Shoutouts to R.Danny for this code.
            commands_used_des = '\n'.join(f'{self.number_places[index]}: {command_name} (used {cmd_uses} times)'
                                          for (index, (command_name, cmd_uses)) in enumerate(fetched))
            embed = discord.Embed(title="Popular Commands", color=0x841d6e)
            embed.add_field(name="All Time", value=commands_used_des)
            query = """SELECT command_name,
                        COUNT (*) as "cmd_uses"
                       FROM commands_usage
                       WHERE used_at > (timezone('UTC', now()) - INTERVAL '1 day')
                       GROUP BY command_name
                       ORDER BY "cmd_uses" DESC
                       LIMIT 10;
                    """
            async with self.bot.db.acquire() as con:
                fetched = await con.fetch(query)
            commands_used_des = '\n'.join(f'{self.number_places[index]}: {command_name} (used {cmd_uses} times)'
                                          for (index, (command_name, cmd_uses)) in enumerate(fetched))
            embed.add_field(name="Today", value=commands_used_des)
            await ctx.send(embed=embed)

    async def message_info_embed(self, msg):
        embed = discord.Embed(timestamp=msg.created_at)
        if msg.author.nick:
            author_name = f"{msg.author.display_name} ({msg.author})"
        else:
            author_name = msg.author
        embed.set_author(name=author_name, icon_url=msg.author.avatar_url)
        embed.set_footer(text=f"#{msg.channel}")
        # if len(msg.content) >= 1500:
        #    url = await self.bot.haste(msg.content)
        #    description = f"Message too long. See the haste -> {url}"
        # else:
        description = msg.content
        if msg.attachments:
            attach_urls = []
            for attachment in msg.attachments:
                attach_urls.append(f'[{attachment.filename}]({attachment.url})')
            description += '\n\N{BULLET} ' + '\n\N{BULLET} '.join(attach_urls)
        description += f"\n\n[Jump to message]({msg.jump_url})"
        if msg.embeds:
            description += "\n • Message has an embed"
        embed.description = description
        return embed

    @commands.group(aliases=['messageinfo', 'msgtext'], invoke_without_command=True)
    async def quote(self, ctx, message_id: int, channel: ReadableChannel = None):
        """Quotes a message"""
        if channel is None:
            channel = ctx.channel
        msg = discord.utils.get(ctx.bot.cached_messages, id=message_id)
        if msg is None:
            try:
                msg = await channel.fetch_message(message_id)
            except discord.NotFound:
                raise MessageNotFoundInChannel(message_id, channel)
            except discord.Forbidden:
                raise ChannelPermissionFailure(f"I don't have permission to view {channel.mention}.")
        embed = await self.message_info_embed(msg)
        if msg.author.color.value != 0:
            embed.color = msg.author.color
        await ctx.send(embed=embed)

    @quote.command(name="raw", aliases=['json'])
    async def msg_raw(self, ctx, message_id: int, channel: ReadableChannel = None):
        # This technically falls under what I wanted quote to do so :dealwithit:
        """Shows raw JSON for a message.

        This escapes markdown formatted text if in the text."""
        if channel is None:
            channel = ctx.channel
        try:
            message = await ctx.bot.http.get_message(channel.id, message_id)
        except discord.NotFound:
            raise MessageNotFoundInChannel(message_id, channel)
        message['content'] = discord.utils.escape_markdown(message['content'])
        if message['embeds']:
            for em in message['embeds']:
                if "description" in em:
                    em['description'] = discord.utils.escape_markdown(em['description'])
        msgr = json.dumps(message, indent=2, sort_keys=True)
        p = TextPages(ctx, msgr, prefix="```json\n")
        await p.paginate()

    async def command_insert(self, ctx):
        """Function to insert command info into self.data_todump"""
        if ctx.guild is None:
            guild_id = None
        else:
            guild_id = ctx.guild.id
        async with self.dump_lock:
            self.data_todump.append({
                'guild_id': guild_id,
                'user_id': ctx.author.id,
                'used_at': ctx.message.created_at.isoformat(),
                'command_name': ctx.command.qualified_name,
                'failure': ctx.command_failed,
            })

    async def bulk_database_insert(self):
        """Inserts data into the database if any bulk data exists"""
        query = """INSERT INTO commands_usage (guild_id, user_id, used_at, command_name, failure)
                   SELECT data.guild_id, data.user_id, data.used_at, data.command_name, data.failure
                   FROM jsonb_to_recordset($1::jsonb) AS
                   data(guild_id BIGINT, user_id BIGINT, used_at TIMESTAMP,
                        command_name TEXT, failure BOOLEAN)
                """
        # If pending data
        if self.data_todump:
            await self.bot.db.execute(query, json.dumps(self.data_todump))
            total = len(self.data_todump)
            # Let's log on more than 1 command
            if total > 1:
                self.bot.log.info(f'{total} commands were added to the database.')
            self.data_todump.clear()

    @tasks.loop(seconds=15.0)
    async def bulk_command_insertion(self):
        async with self.dump_lock:
            await self.bulk_database_insert()
        # Reset command spammers as well
        self.bot.command_spammers = {}

    @commands.Cog.listener()
    async def on_command_completion(self, ctx):
        await self.command_insert(ctx)

    async def send_guild_info(self, embed, guild):
        bots = sum(member.bot for member in guild.members)
        humans = guild.member_count - bots
        embed.add_field(name='Guild Name', value=guild.name)
        embed.add_field(name='Guild ID', value=guild.id)
        embed.add_field(name='Member Count', value=f"Bots: {bots}\nHumans: {humans}")
        embed.add_field(name='Owner', value=f"{guild.owner} | ID: {guild.owner.id}")
        wbhk = discord.Webhook.from_url
        adp = discord.AsyncWebhookAdapter(self.bot.aiosession)
        webhook = wbhk(self.bot.config['logging']['guild_alerts'], adapter=adp)
        await webhook.execute(embed=embed)

    @commands.Cog.listener()
    async def on_guild_join(self, guild):
        embed = discord.Embed(title="Joined New Guild", color=discord.Color.blue())
        await self.send_guild_info(embed, guild)

    @commands.Cog.listener()
    async def on_guild_remove(self, guild):
        embed = discord.Embed(title="Left Guild", color=discord.Color.red())
        self.bot.log.info(f"Left Guild | {guild.name} | {guild.id}")
        await self.send_guild_info(embed, guild)

    @commands.Cog.listener()
    async def on_guild_unavailable(self, guild):
        if not self.bot.is_ready():
            return
        if guild.id in self.unavailable_guilds:
            return
        embed = discord.Embed(title="🚧 Guild Unavailable",
                              color=discord.Color.red())
        self.bot.log.info(f"🚧 Guild Unavailable | {guild.name} "
                          f"| {guild.id}")
        try:
            self.unavailable_guilds.append(guild.id)
        except ValueError:
            return
        await self.send_guild_info(embed, guild)

    @commands.Cog.listener()
    async def on_guild_available(self, guild):
        if not self.bot.is_ready():
            return
        embed = discord.Embed(title="✅ Guild Available",
                              color=discord.Color.green())
        self.bot.log.info(f"✅ Guild Available | {guild.name} "
                          f"| {guild.id}")
        try:
            self.unavailable_guilds.remove(guild.id)
        except ValueError:
            return
        await self.send_guild_info(embed, guild)


def setup(bot):
    bot.add_cog(Meta(bot))
