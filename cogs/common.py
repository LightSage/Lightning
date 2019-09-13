# Whole Imported Cog from robocop-ng. with the removal of some things that won't be used.
# MIT License
#
# Copyright (c) 2018 Arda "Ave" Ozkal
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

import asyncio
import traceback
import datetime
import arrow
import time
import math
import parsedatetime
import subprocess
from discord.ext.commands import Cog
import discord
import json


class Common(Cog):
    def __init__(self, bot):
        self.bot = bot
        self.bot.slice_message = self.slice_message
        self.max_split_length = 3
        self.bot.hex_to_int = self.hex_to_int
        self.bot.download_file = self.download_file
        self.bot.aiojson = self.aiojson
        self.bot.aioget = self.aioget
        self.bot.aiogetbytes = self.aiogetbytes
        self.bot.get_relative_timestamp = self.get_relative_timestamp
        self.bot.escape_message = self.escape_message
        self.bot.parse_time = self.parse_time
        self.bot.haste = self.haste
        self.bot.call_shell = self.call_shell
        self.bot.get_utc_timestamp = self.get_utc_timestamp
        self.bot.humanized_time = self.humanized_time
        self.bot.create_error_ticket = self.create_error_ticket

    async def create_error_ticket(self, ctx, title, information):
        query = """INSERT INTO bug_tickets (status, ticket_info, created)
                   VALUES ($1, $2, $3)
                   RETURNING id;
                """
        ext = {"text": information, "author_id": ctx.author.id}
        async with self.bot.db.acquire() as con:
            id = await con.fetchrow(query, "Received", json.dumps(ext), datetime.datetime.utcnow())
        e = discord.Embed(title=f"{title} Report - ID: {id[0]}", description=information)
        e.set_author(name=ctx.author, icon_url=ctx.author.avatar_url)
        e.timestamp = datetime.datetime.utcnow()
        e.set_footer(text="Status: Received")
        ch = self.bot.get_channel(self.bot.config.bug_reports_channel)
        msg = await ch.send(embed=e)
        query = """UPDATE bug_tickets
                   SET guild_id=$2, channel_id=$3, message_id=$4
                   WHERE id=$1;
                """
        async with self.bot.db.acquire() as con:
            await con.execute(query, id[0], msg.guild.id, msg.channel.id, msg.id)
        msg = f"Created a bug ticket with ID {id[0]}. "\
              "You can see updates on your ticket by joining "\
              "the [support server](https://discord.gg/cDPGuYd) and looking in the "\
              f"reports channel."
        embed = discord.Embed(title="Uh oh, my powers overloaded.", description=msg)
        embed.set_footer(text="My developers have been notified about this.")
        await ctx.send(embed=embed)

    def humanized_time(self, time_from=None, time_to=None, distance=True,
                       include_timedate=False):
        if not time_from:
            time_from = arrow.utcnow()
        if not time_to:
            time_to = arrow.utcnow()
        arrow_time = arrow.get(time_to)
        if distance is True:
            str_ret = arrow_time.humanize(time_from, only_distance=True)
        else:
            str_ret = arrow_time.humanize(time_from)
        if include_timedate is True:
            return f"{str_ret} ({str(time_to).split('.')[0]} UTC)"
        return str_ret

    def parse_time(self, delta_str):
        cal = parsedatetime.Calendar()
        time_struct, parse_status = cal.parse(delta_str)
        res_timestamp = math.floor(time.mktime(time_struct))
        return res_timestamp

    def get_relative_timestamp(self, time_from=None, time_to=None,
                               humanized=False, include_from=False,
                               include_to=False):
        # Setting default value to utcnow() makes it show time from cog load
        # which is not what we want
        if not time_from:
            time_from = arrow.utcnow()
        if not time_to:
            time_to = arrow.utcnow()
        if humanized:
            arrow_time = arrow.get(time_to)
            humanized_string = arrow_time.humanize(time_from)
            if include_from and include_to:
                str_with_from_and_to = f"{humanized_string} "\
                                       f"({str(time_from).split('.')[0]} "\
                                       f"- {str(time_to).split('.')[0]})"
                return str_with_from_and_to
            elif include_from:
                str_with_from = f"{humanized_string} "\
                                f"({str(time_from).split('.')[0]} UTC)"
                return str_with_from
            elif include_to:
                str_with_to = f"{humanized_string} "\
                              f"({str(time_to).split('.')[0]} UTC)"
                return str_with_to
            return humanized_string
        else:
            epoch = datetime.datetime.utcfromtimestamp(0)
            epoch_from = (time_from - epoch).total_seconds()
            epoch_to = (time_to - epoch).total_seconds()
            second_diff = epoch_to - epoch_from
            result_string = str(datetime.timedelta(
                seconds=second_diff)).split('.')[0]
            return result_string

    def get_utc_timestamp(self, time_from=None, time_to=None,
                          include_from=False,
                          include_to=False):
        # Setting default value to utcnow() makes it show time from cog load
        # which is not what we want
        if not time_from:
            time_from = datetime.datetime.utcnow()
        if not time_to:
            time_to = datetime.datetime.utcnow()
        if include_from and include_to:
            str_with_from_and_to = f"{str(time_from).split('.')[0]} "\
                                   f"- {str(time_to).split('.')[0]}"
            return str_with_from_and_to
        elif include_from:
            str_with_from = f"{str(time_from).split('.')[0]} UTC"
            return str_with_from
        elif include_to:
            str_with_to = f"{str(time_to).split('.')[0]} UTC"
            return str_with_to
        else:
            epoch = datetime.datetime.utcfromtimestamp(0)
            epoch_from = (time_from - epoch).total_seconds()
            epoch_to = (time_to - epoch).total_seconds()
            second_diff = epoch_to - epoch_from
            result_string = str(datetime.timedelta(
                seconds=second_diff)).split('.')[0]
            return result_string

    async def aioget(self, url):
        try:
            data = await self.bot.aiosession.get(url)
            if data.status == 200:
                text_data = await data.text()
                self.bot.log.info(f"Data from {url}: {text_data}")
                return text_data
            else:
                self.bot.log.error(f"HTTP Error {data.status} "
                                   "while getting {url}")
        except Exception:
            self.bot.log.error(f"Error while getting {url} "
                               f"on aiogetbytes: {traceback.format_exc()}")

    async def aiogetbytes(self, url):
        try:
            data = await self.bot.aiosession.get(url)
            if data.status == 200:
                byte_data = await data.read()
                self.bot.log.debug(f"Data from {url}: {byte_data}")
                return byte_data
            else:
                self.bot.log.error(f"HTTP Error {data.status} "
                                   f"while getting {url}")
                return False
        except Exception:
            self.bot.log.error(f"Error while getting {url} "
                               f"on aiogetbytes: {traceback.format_exc()}")

    async def aiojson(self, url):
        try:
            data = await self.bot.aiosession.get(url)
            if data.status == 200:
                text_data = await data.text()
                self.bot.log.info(f"Data from {url}: {text_data}")
                content_type = data.headers['Content-Type']
                return await data.json(content_type=content_type)
            else:
                self.bot.log.error(f"HTTP Error {data.status} "
                                   f"while getting {url}")
                return False
        except Exception:
            self.bot.log.error(f"Error while getting {url} "
                               f"on aiogetbytes: {traceback.format_exc()}")
            return False

    def hex_to_int(self, color_hex: str):
        """Turns a given hex color into an integer"""
        return int("0x" + color_hex.strip('#'), 16)

    def escape_message(self, text: str):
        """Escapes unfun stuff from messages"""
        return str(text).replace("@", "@ ").replace("<#", "# ")

    # This function is based on https://stackoverflow.com/a/35435419/3286892
    # by link2110 (https://stackoverflow.com/users/5890923/link2110)
    # modified by Ave (https://github.com/aveao), licensed CC-BY-SA 3.0
    async def download_file(self, url, local_filename):
        file_resp = await self.bot.aiosession.get(url)
        file = await file_resp.read()
        with open(local_filename, "wb") as f:
            f.write(file)

    # 2000 is maximum limit of discord
    async def slice_message(self, text, size=2000, prefix="", suffix=""):
        """Slices a message into multiple messages"""
        if len(text) > size * self.max_split_length:
            haste_url = await self.haste(text)
            return [f"Message exceeded the max split "
                    f"length"
                    f", go to haste: <{haste_url}>"]
        reply_list = []
        size_wo_fix = size - len(prefix) - len(suffix)
        while len(text) > size_wo_fix:
            reply_list.append(f"{prefix}{text[:size_wo_fix]}{suffix}")
            text = text[size_wo_fix:]
        reply_list.append(f"{prefix}{text}{suffix}")
        return reply_list

    async def haste(self, text, instance='https://mystb.in/'):
        response = await self.bot.aiosession.post(f"{instance}documents",
                                                  data=text)
        if response.status == 200:
            result_json = await response.json()
            return f"{instance}{result_json['key']}"
        else:
            self.bot.log.error(f"{response.text}")
            return f"Error {response.status}. Try again later?"

    # The function (call_shell) listed below is my work (LightSage).
    # LICENSE: GNU Affero General Public License v3.0
    # https://github.com/LightSage/Lightning.py/blob/master/LICENSE
    async def call_shell(self, shell_command: str):
        try:
            pipe = asyncio.subprocess.PIPE
            process = await asyncio.create_subprocess_shell(shell_command,
                                                            stdout=pipe,
                                                            stderr=pipe)
            stdout, stderr = await process.communicate()
        except NotImplementedError:  # Account for Windows (Trashdows)
            process = subprocess.Popen(shell_command, shell=True,
                                       stdout=subprocess.PIPE,
                                       stderr=subprocess.PIPE)
            stdout, stderr = process.communicate()

        if stdout and stderr:
            return f"$ {shell_command}\n\n[stderr]\n"\
                   f"{stderr.decode('utf-8')}\n===\n"\
                   f"[stdout]\n{stdout.decode('utf-8')}"
        elif stdout:
            return f"$ {shell_command}\n\n"\
                   f"[stdout]\n{stdout.decode('utf-8')}"
        elif stderr:
            return f"$ {shell_command}\n\n"\
                   f"[stderr]\n{stderr.decode('utf-8')}"


def setup(bot):
    bot.add_cog(Common(bot))
