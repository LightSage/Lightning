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

from discord.ext import commands
import discord

class SafeSend(commands.Converter):
    async def convert(self, ctx, message):
        # Extra Converter to save my life. Fuck @everyone pings
        # I hope this saves my life forever. :blobsweat:
        content = await commands.clean_content().convert(ctx, str(message))
        return content

class LastImage(commands.Converter):
    """Converter to handle images"""
    async def default(self, ctx, param):
        async for message in ctx.channel.history(limit=15):
            # Capping it off at 15 for safety measures
            for embed in message.embeds:
                if embed.thumbnail and embed.thumbnail.proxy_url:
                    return embed.thumbnail.proxy_url
            for attachment in message.attachments:
                if attachment.proxy_url:
                    return attachment.proxy_url
        raise discord.ext.errors.MissingRequiredArgument("Couldn't not "
                                                         "find an image in the last "
                                                         "15 messages")
