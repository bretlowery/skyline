# -*- coding: utf-8 -*-
#
# agent.py
#
# Derived from
#
# Graphite Carbon
#
# and
#
# pygtail - a python "port" of logtail2
# Copyright (C) 2011 Brad Greenlee <brad@footle.org>
#
# Derived from logcheck <http://logcheck.org>
# Copyright (C) 2003 Jonathan Middleton <jjm@ixtab.org.uk>
# Copyright (C) 2001 Paul Slootman <paul@debian.org>
#

from __future__ import print_function
from os import fstat, stat
import os
from os.path import exists, getsize
import sys
from sys import getsizeof
import glob
import gzip
from optparse import OptionParser
import datetime
import struct
from socket import socket
import re
import time
import json
import user_agents
import zlib
import platform
try:
    import cpickle as pickle
except:
    import pickle
from Crypto.Cipher import AES

__version__ = '0.0.1'

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'

# DO NOT CHANGE THESE CONSTANTS AT ALL EVER
# See http://www.isthe.com/chongo/tech/comp/fnv/index.html for math-y details.
FNV_64_PRIME = 1099511628211
FNV1_64A_INIT = 14695981039346656037
BIGGEST_64_INT = 9223372036854775807
SMALLEST_64_INT = -9223372036854775808

MONTHS = {
    'Jan': 1,
    'Feb': 2,
    'Mar': 3,
    'Apr': 4,
    'May': 5,
    'Jun': 6,
    'Jul': 7,
    'Aug': 8,
    'Sep': 9,
    'Oct': 10,
    'Nov': 11,
    'Dec': 12
}

REQUESTMETHODS = ["GET", "POST", "HEAD", "PUT", "DELETE", "OPTIONS", "TRACE", "CONNECT", "PATCH"]

TAGPATTERN = re.compile(r"(\"%.+?\")", re.IGNORECASE)

sock = socket()

# ENCRYPTER = AES.new('')

# BOTLIST = []

PY3 = sys.version_info[0] == 3

if PY3:
    text_type = str
else:
    text_type = unicode


def force_text(s, encoding='utf-8', errors='strict'):
    if isinstance(s, text_type):
        return s
    return s.decode(encoding, errors)


class Pygtail(object):
    """
    Creates an iterable object that returns only unread lines.

    Keyword arguments:
    offset_file   File to which offset data is written (default: <logfile>.offset).
    commitperline      Update the offset file every time we read a line (as opposed to
                  only when we reach the end of the file (default: False))
    every_n       Update the offset file every n'th line (as opposed to only when
                  we reach the end of the file (default: 0))
    on_update     Execute this function when offset data is written (default False)
    copytruncate  Support copytruncate-style log rotation (default: True)
    rotation_patterns  List of custom rotated log patterns to match (default: None)
    """
    def __init__(self, filename, offset_file=None, commitperline=False, copytruncate=True,
                 every_n=0, on_update=False, read_from_end=False, rotation_patterns=None):
        self.filename = filename
        self.commitperline = commitperline
        self.every_n = every_n
        self.on_update = on_update
        self.copytruncate = copytruncate
        self.read_from_end = read_from_end
        self.rotation_patterns = rotation_patterns
        self._offset_file = offset_file or "%s.offset" % self.filename
        self._offset_file_inode = 0
        self._offset = 0
        self._since_update = 0
        self._fh = None
        self._rotated_logfile = None

        # if offset file exists and non-empty, open and parse it
        if exists(self._offset_file) and getsize(self._offset_file):
            offset_fh = open(self._offset_file, "r")
            (self._offset_file_inode, self._offset) = \
                [int(line.strip()) for line in offset_fh]
            offset_fh.close()
            if self._offset_file_inode != stat(self.filename).st_ino or \
                    stat(self.filename).st_size < self._offset:
                # The inode has changed or filesize has reduced so the file
                # might have been rotated.
                # Look for the rotated file and process that if we find it.
                self._rotated_logfile = self._determine_rotated_logfile()

    def __del__(self):
        if self._filehandle():
            self._filehandle().close()

    def __iter__(self):
        return self

    def next(self):
        """
        Return the next line in the file, updating the offset.
        """
        try:
            line = self._get_next_line()
        except StopIteration:
            # we've reached the end of the file; if we're processing the
            # rotated log file or the file has been renamed, we can continue with the actual file; otherwise
            # update the offset file
            if self._is_new_file():
                self._rotated_logfile = None
                self._fh.close()
                self._offset = 0
                # open up current logfile and continue
                try:
                    line = self._get_next_line()
                except StopIteration:  # oops, empty file
                    self._update_offset_file()
                    raise
            else:
                self._update_offset_file()
                raise

        if self.commitperline:
            self._update_offset_file()
        elif self.every_n and self.every_n <= self._since_update:
            self._update_offset_file()

        return line

    def __next__(self):
        """`__next__` is the Python 3 version of `next`"""
        return self.next()

    def readlines(self):
        """
        Read in all unread lines and return them as a list.
        """
        return [line for line in self]

    def read(self):
        """
        Read in all unread lines and return them as a single string.
        """
        lines = self.readlines()
        if lines:
            try:
                return ''.join(lines)
            except TypeError:
                return ''.join(force_text(line) for line in lines)
        else:
            return None

    def _is_closed(self):
        if not self._fh:
            return True
        try:
            return self._fh.closed
        except AttributeError:
            if isinstance(self._fh, gzip.GzipFile):
                # python 2.6
                return self._fh.fileobj is None
            else:
                raise

    def _filehandle(self):
        """
        Return a filehandle to the file being tailed, with the position set
        to the current offset.
        """
        if not self._fh or self._is_closed():
            filename = self._rotated_logfile or self.filename
            if filename.endswith('.gz'):
                self._fh = gzip.open(filename, 'r')
            else:
                self._fh = open(filename, "r", 1)
            if self.read_from_end and not exists(self._offset_file):
                self._fh.seek(0, os.SEEK_END)
            else:
                self._fh.seek(self._offset)

        return self._fh

    def _update_offset_file(self):
        """
        Update the offset file with the current inode and offset.
        """
        if self.on_update:
            self.on_update()
        offset = self._filehandle().tell()
        inode = stat(self.filename).st_ino
        fh = open(self._offset_file, "w")
        fh.write("%s\n%s\n" % (inode, offset))
        fh.close()
        self._since_update = 0

    def _determine_rotated_logfile(self):
        """
        We suspect the logfile has been rotated, so try to guess what the
        rotated filename is, and return it.
        """
        rotated_filename = self._check_rotated_filename_candidates()
        if rotated_filename and exists(rotated_filename):
            if stat(rotated_filename).st_ino == self._offset_file_inode:
                return rotated_filename

            # if the inode hasn't changed, then the file shrank; this is expected with copytruncate,
            # otherwise print a warning
            if stat(self.filename).st_ino == self._offset_file_inode:
                if self.copytruncate:
                    return rotated_filename
                else:
                    sys.stderr.write(
                        "[pygtail] [WARN] file size of %s shrank, and copytruncate support is "
                        "disabled (expected at least %d bytes, was %d bytes).\n" %
                        (self.filename, self._offset, stat(self.filename).st_size))

        return None

    def _check_rotated_filename_candidates(self):
        """
        Check for various rotated logfile filename patterns and return the first
        match we find.
        """
        # savelog(8)
        candidate = "%s.0" % self.filename
        if (exists(candidate) and exists("%s.1.gz" % self.filename) and
            (stat(candidate).st_mtime > stat("%s.1.gz" % self.filename).st_mtime)):
            return candidate

        # logrotate(8)
        # with delaycompress
        candidate = "%s.1" % self.filename
        if exists(candidate):
            return candidate

        # without delaycompress
        candidate = "%s.1.gz" % self.filename
        if exists(candidate):
            return candidate

        rotated_filename_patterns = [
            # logrotate dateext rotation scheme - `dateformat -%Y%m%d` + with `delaycompress`
            "%s-[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9]",
            # logrotate dateext rotation scheme - `dateformat -%Y%m%d` + without `delaycompress`
            "%s-[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9].gz",
            # logrotate dateext rotation scheme - `dateformat -%Y%m%d-%s` + with `delaycompress`
            "%s-[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9]-[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9]",
            # logrotate dateext rotation scheme - `dateformat -%Y%m%d-%s` + without `delaycompress`
            "%s-[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9]-[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9].gz",
            # for TimedRotatingFileHandler
            "%s.[0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]",
        ]
        if self.rotation_patterns:
            rotated_filename_patterns.extend(self.rotation_patterns)

        # break into directory and filename components to support cases where the
        # the file is prepended as part of rotation
        file_dir, rel_filename = os.path.split(self.filename)
        for rotated_filename_pattern in rotated_filename_patterns:
            candidates = glob.glob(os.path.join(file_dir, rotated_filename_pattern % rel_filename))
            if candidates:
                candidates.sort()
                return candidates[-1]  # return most recent

        # no match
        return None

    def _is_new_file(self):
        # Processing rotated logfile or at the end of current file which has been renamed
        return self._rotated_logfile or \
               self._filehandle().tell() == fstat(self._filehandle().fileno()).st_size and \
               fstat(self._filehandle().fileno()).st_ino != stat(self.filename).st_ino

    def _get_next_line(self):
        line = self._filehandle().readline()
        if not line:
            raise StopIteration
        self._since_update += 1
        return line


class Carbonizer(object):
    def __init__(self, *args, **kwargs):
        global __version__
        self.conf = kwargs.pop('conf')
        self.strict = kwargs.pop('strict')
        self.lines = []
        self.numlines = 0
        self.pygtail = kwargs.pop('pygtail')
        if self.pygtail:
            try:
                self.lines = self.pygtail.readlines()
                self.numlines = len(self.lines)
                self.totbytesin = getsizeof(self.lines)
            except Exception as e:
                raise IOError("FAILED to read the log file: %s" % str(e))
        self.observations = None
        self.metadata = None
        self.numobservations = 0
        self.nummetrics = 0
        self.totbytespackaged = 0
        self.totbytessent = 0
        self.logregex = self._get_loglineregex()
        self.currentua = None

    @property
    def server_name(self):
        return os.getenv('HOSTNAME', os.getenv('COMPUTERNAME', platform.node())).split('.')[0]

    @staticmethod
    def _get_hash(string):
        """
        FNV1a hash algo. Generates a (signed) 64-bit FNV1a hash.
        See http://www.isthe.com/chongo/tech/comp/fnv/index.html for math-y details.
        """
        encoded_trimmed_string = string.strip().encode('utf8')
        assert isinstance(encoded_trimmed_string, bytes)
        i64 = FNV1_64A_INIT
        byte_array = bytearray(encoded_trimmed_string)
        for byte in byte_array:
            i64 = i64 ^ byte
            i64 = (i64 * FNV_64_PRIME) % (2 ** 64)
        # wrap the result into the full signed BIGINT range of the underlying persistence system
        if i64 > BIGGEST_64_INT:
            i64 = SMALLEST_64_INT + (i64 - BIGGEST_64_INT - 1)  # optimized CPU ops
        return "1"+str(i64) if i64 >= 0 else "2" + str(abs(i64+1))

    def _get_loglineregex(self):
        patterns = {}
        for field in self.conf["fields"]:
            patterns[str(field["name"]).lstrip("$")] = str(field["regex"])
        try:
            reexpr = ''.join(
                    '(?P<%s>%s)' % (g, patterns.get(g, '.*?')) if g else re.escape(c)
                    for g, c in re.findall(r'\$(\w+)|(.)', str(self.conf["format"])))
            return re.compile(reexpr)
        except:
            raise IOError("carbonizer.json has an incorrect or incomplete Format field value. Aborting.")

    def _parse_logline(self, line, lineno):
        m = None
        line = line.rstrip()
        try:
            m = self.logregex.match(line)
        except Exception as e:
            if self.strict:
                raise IOError("Halting on line %d (--strict specified): %s." % (lineno, str(e)))
            print("Skipping line %d: %s..." % (lineno, str(e)))
            pass
        if m:
            return m.groupdict()
        else:
            return None

    @staticmethod
    def _get_value(values, metric):
        return values[metric.lstrip("$")]

    def _get_mask(self, element):
        mask = None
        for field in self.conf["fields"]:
            if field["name"] == element:
                mask = field["output"]
                break
        if mask == "":
            mask = None
        return mask

    def _get_timestamp(self, values):

        def _ts_to_dts(ts):
            global MONTHS
            try:
                dts = str(datetime.datetime(int(ts[7:11]), MONTHS[ts[3:6]], int(ts[0:2]), int(ts[12:14]), int(ts[15:17]), int(ts[18:20])))
            except:
                dts = None
            return dts

        return _ts_to_dts(self._get_value(values, self.conf["timestamp"]))

    def _parse_ua(self, value):
        if not self.currentua:
            self.currentua = user_agents.parse(value.lstrip('\"').rstrip('\"'))

    def _get_ua_component(self, string, tag, component):
        try:
            if self.currentua.ua_string == "-":
                return string.replace(tag, "MISSING")
            else:
                val = str(component)
                if not val:
                    val = "UNKNOWN"
                else:
                    val = val.replace("Other", "UNKNOWN").replace("None", "UNKNOWN")
                return string.replace(tag, val)
        except:
            pass
        return string.replace(tag, "UNKNOWN")

    def _format_value(self, string, tag, value):
        if tag == '%s':
            return string.replace(tag, value)
        elif tag == '%a24' or tag == '%a16':
            substrings = value.split(".")
            if tag == '%a24':
                value = '%s.%s.%s.0' % (substrings[0], substrings[1], substrings[2])
            else:
                value = '%s.%s.0.0' % (substrings[0], substrings[1])
            return string.replace(tag, value)
        elif tag == '%rt' or tag == '%rp':
            value = value.lstrip('\"').rstrip('\"')
            splitsville = value.split(" ", 1)
            if splitsville[0] in REQUESTMETHODS:
                if tag == "%rt":
                    return string.replace("%rt", splitsville[0])
                else:
                    return string.replace("%rp", splitsville[1])
            if tag == "%rt":
                return string.replace("%rt", "?")
            else:
                return string.replace("%rp", value)
        elif tag == "%bf":
            self._parse_ua(value)
            return self._get_ua_component(string, tag, self.currentua.browser.family)
        elif tag == "%bv":
            self._parse_ua(value)
            return self._get_ua_component(string, tag, self.currentua.browser.version_string)
        elif tag == "%of":
            self._parse_ua(value)
            return self._get_ua_component(string, tag, self.currentua.os.family)
        elif tag == "%ov":
            self._parse_ua(value)
            return self._get_ua_component(string, tag, self.currentua.os.version_string)
        elif tag == "%df":
            self._parse_ua(value)
            return self._get_ua_component(string, tag, self.currentua.device.family)
        elif tag == "%db":
            self._parse_ua(value)
            return self._get_ua_component(string, tag, self.currentua.device.brand)
        elif tag == "%dm":
            self._parse_ua(value)
            return self._get_ua_component(string, tag, self.currentua.device.model)
        elif tag == "%mob":
            self._parse_ua(value)
            return self._get_ua_component(string, tag, self.currentua.is_mobile)
        elif tag == "%tab":
            self._parse_ua(value)
            return self._get_ua_component(string, tag, self.currentua.is_tablet)
        elif tag == "%pc":
            self._parse_ua(value)
            return self._get_ua_component(string, tag, self.currentua.is_tablet)
        # the bot property is *not* reliable, determine this on the backend instead
        #elif tag == "%bot":
        #    self._parse_ua(value)
        #    is_bot = self.currentua.is_bot
        #    return self._get_ua_component(string, tag, is_bot)
        else:
            raise ValueError("Unknown or unsupported mask tag \"%s\"." % tag)

    def _get_metric(self, values):
        metric = self.conf["metric"]
        elements = metric.split()
        for element in elements:
            value = self._get_value(values, element)
            output = self._get_mask(element)
            for match in TAGPATTERN.findall(output):
                tag = match.lstrip('"').rstrip('"')
                output = self._format_value(output, tag, value)
            metric = metric.replace(element, output)
        return "{%s}" % metric.replace("} {", "}, {")

    def _get_headers(self, hostname, port, options):
        transport = "pulsar" if options.send_to_pulsar else "carbon"
        return '{"headers" : ' \
               '{"to": {"key": "%s", "protocol": "%s", "host": "%s", "port": "%s"}},' \
               '{"from": {"key": "%s", "servername": "%s"}}' \
               '}' \
               % (self._get_hash("%s.%s.%s" % (transport, hostname, port)), transport, hostname, port,
                  self._get_hash(self.server_name), self.server_name)

    def _pickler(self, rawcucumbers):
        picklejar = pickle.dumps(rawcucumbers, protocol=2)
        lid = struct.pack("!L", len(picklejar))
        return lid + picklejar

    def _print_observations(self, observations, metadata):
        # sort in chronological order of the first occurrence of each metric,
        # then chronologically within each metric
        keys = sorted(observations.keys(), key=lambda tup: (tup[1], tup[0]))
        for key in keys:
            metric = key[0][5:]
            print(bcolors.OKGREEN + bcolors.BOLD + "Metric %s" % metric + bcolors.ENDC + "\r\n" +
                  bcolors.OKBLUE + "   Headers" + bcolors.ENDC + "\r\n      %s\r\n" % metadata[metric][0] +
                  bcolors.OKBLUE + "   Data" + bcolors.ENDC + "\r\n      %s" % metadata[metric][2])
            print(bcolors.OKBLUE + "   Event(s)" + bcolors.ENDC)
            print("      %s:   %d" % (key[1], int(observations[key])))  # 1st occurrence of the metric
            for nextkey in keys:
                if nextkey[0][5:] == metric:
                    if nextkey[1] > key[1]:
                        if observations[nextkey] > 0:
                            print("      %s:   %d" % (nextkey[1], int(observations[nextkey])))  # each subsequent occurrence in order
                            observations[nextkey] = 0
            print(" ")

    def package(self, hostname, port, options):
        start = time.time()
        metric_definition = "%s" % self.conf["metric"]
        if not options.test:
            metric_definition = zlib.compress(metric_definition, 9)
        headers = self._get_headers(hostname, port, options)
        if not options.test:
            headers = zlib.compress(headers, 9)
        observations = {}
        metadata = {}
        i = 0
        for line in self.lines:
            i += 1
            values = self._parse_logline(line, i)
            if values:
                timestamp = self._get_timestamp(values)
                self.currentua = None  # we're about to get it
                metric = self._get_metric(values)
                hash = self._get_hash(metric)
                path = 'czir.' + hash
                key = (path, timestamp)
                if key in observations.keys():
                    observations[key] += 1
                else:
                    observations[key] = 1
                if hash not in metadata.keys():
                    if options.test:
                        metadata[hash] = (headers, metric_definition, metric)
                    else:
                        metadata[hash] = (headers, metric_definition, zlib.compress(metric, 9))

        if options.raw:
            self.observations = [(key[0], (key[1], observations[key])) for key in observations.keys()].sort(key=lambda tup: (tup[0][1], tup[0][0]))
        else:
            self.observations = self._pickler([(key[0], (key[1], observations[key])) for key in observations.keys()])
        # self.metadata.sort(key=lambda tup: (tup[0]))  # by hashed path value
        if options.raw:
            self.metadata = [("czir.%s" % key, metadata[key]) for key in metadata.keys()].sort(key=lambda tup: (tup[0]))
        else:
            self.metadata = self._pickler([("czir.%s" % key, metadata[key]) for key in metadata.keys()])

        self.numobservations = len(self.observations)
        self.nummetrics = len(self.metadata)
        self.totbytespackaged = getsizeof(self.observations) + getsizeof(self.metadata)

        elapsed = time.time() - start
        if elapsed < 1.0:
            print("   <1s elapsed")
        else:
            print("   %ds elapsed" % elapsed)
        print("   %d unique metrics (%d/sec)" % (self.nummetrics, self.nummetrics / elapsed))
        print("   %d total observations (%d/sec)" % (self.numobservations, self.numobservations / elapsed))
        print("   %d bytes %s (%d/sec)" % (self.totbytespackaged, "packaged" if options.test else "packaged and compressed", self.totbytespackaged / elapsed))
        if options.test:
            print("   No compression was used because TEST MODE was specified.")
            print(" ")
            self._print_observations(observations, metadata)
        return


def main():
    global sock
    # command-line parsing
    cmdline = OptionParser(usage="usage: %prog [options] logfile outputhostname outputport",
                           description="Send aggregated log file metrics from as-yet-unread log file lines to Carbon client or relay.")
    cmdline.add_option("--offset-file", "-o",
                       action="store",
                       help="File to which offset data is written (default: <logfile>.offset).")
    cmdline.add_option("--commitperline", "-l",
                       action="store_true",
                       help="Update the offset file every time we read a line (as opposed to"
                            " only when we reach the end of the file).")
    cmdline.add_option("--every-n", "-n",
                       action="store",
                       help="Update the offset file every n'th time we read a line (as opposed to"
                            " only when we reach the end of the file).")
    cmdline.add_option("--no-copytruncate",
                       action="store_true",
                       help="Don't support copytruncate-style log rotation. Instead, if the log file"
                            " shrinks, print a warning.")
    cmdline.add_option("--read-from-end",
                       action="store_true",
                       help="Read log file from the end if offset file is missing. Useful for large files.")
    cmdline.add_option("--rotation-pattern",
                       action="append",
                       help="Custom log rotation glob pattern. Use %s to represent the original filename."
                            " You may use this multiple times to provide multiple patterns.")
    cmdline.add_option("--version",
                       action="store_true",
                       help="Print version and exit.")
    cmdline.add_option("--strict",
                       action="store_true",
                       help="If specified, abort on the first (meaning, 'any and every') non-parsable log line found. "
                            "If not specified (the default), skip all non-parsable log lines but process the rest of the entries.")
    cmdline.add_option("--test",
                       action="store_true",
                       help="If specified, test mode: do not send results to output, just print them to stdout instead.")
    cmdline.add_option("--send-to-carbon", "-c",
                       action="store_true",
                       help="If specified, outputhostname/port is an Apache Carbon relay (the default).")
    cmdline.add_option("--send-to-pulsar", "-p",
                       action="store_true",
                       help="If specified, outputhostname/port specifies a Apache Pulsar consumer.")
    cmdline.add_option("--raw", "-r",
                       action="store_true",
                       help="If specified, sends data in raw (unpickled) format. Applies to non-Carbon targets only; data sent to Carbon targets is always pickled.")

    options, args = cmdline.parse_args()

    if options.version:
        print("carbonizer v", __version__)
        sys.exit(0)

    if len(args) != 3:
        cmdline.error("Please provide a logfile to read, and a Carbon client/relay host and port number to send it to.")

    assert(args[0] and args[1] and args[2])
    assert(len(args[0]) > 0 and len(args[1]) > 0)
    assert(args[2].isdigit())
    assert(0 <= int(args[2]) <= 65535)

    with open(os.path.join(os.path.dirname(__file__), "carbonizer.json"), 'r') as conf_file:
        conf = json.loads(conf_file.read())

    assert(conf["version"] == __version__)
    assert(len(conf["format"]) > 0)
    assert(len(conf["fields"]) > 0)
    assert(len(conf["timestamp"]) > 0)
    assert(len(conf["metric"]) > 0)
    assert(conf["id"] == "%id")

    target = "carbon"
    try:
        if options.send_to_pulsar:
            target = "pulsar"
    except:
        pass

    if options.every_n:
        options.every_n = int(options.every_n)
    if int(args[2]) <= 0:
        options.test = True

    f = args[0].strip()
    tail = Pygtail(f,
                   offset_file=options.offset_file,
                   commitperline=options.commitperline,
                   every_n=options.every_n,
                   copytruncate=not options.no_copytruncate,
                   read_from_end=options.read_from_end,
                   rotation_patterns=options.rotation_pattern)

    if not tail:
        print("No new entries found to process; exiting...")
    else:
        data = Carbonizer(pygtail=tail, conf=conf, strict=options.strict)
        if data.numlines == 0:
            print("No new, parsable entries found to process; exiting...")
        else:
            h = args[1].strip()
            p = int(args[2])
            print("Found 1 entry to package for transport..." if data.numlines == 1 else "Found %d entries to package for transport..." % data.numlines)
            if p > 0 and not options.test:
                data.package(h, p, options)
                if target == "pulsar":
                    import pulsar
                    client = pulsar.Client('pulsar://%s:%s' % (h, p))
                    producer = None
                    if "topic" in data.conf:
                        if data.conf["topic"]:
                            producer = client.create_producer(data.conf["topic"])
                    if not producer:
                        producer = client.create_producer('czir.%s' % __version__)
                    if options.raw:
                        for metric in data.metadata:
                            producer.send(metric)
                        for observation in data.observations:
                            producer.send(observation)
                    else:
                        producer.send(data.metadata)  # .encode('utf-8'))
                        producer.send(data.observations)  # .encode('utf-8'))
                    client.close()
                else:
                    try:
                        print("Connecting to the Carbon daemon at %s:%d..." % (h, p))
                        sock.connect(h, p)
                    except Exception as e:
                        cmdline.error("FAILED to connect to the Carbon daemon: %s" % str(e))
                        exit(1)
                    senderr = False
                    try:
                        print("Connected. Sending...")
                        sock.sendall(data.metadata)
                        sock.sendall(data.observations)
                        print("Done.")
                    except Exception as e:
                        senderr = True
                        cmdline.error("FAILED to send to the Carbon daemon: %s" % str(e))
                    finally:
                        sock.close()
                        if senderr:
                            exit(1)
            elif p <= 0:
                print("** INVALID PORT SPECIFIED, TEST MODE ENABLED, PACKAGING DATA ONLY")
                data.package("localhost", 0, options)
            else:
                print("** TEST MODE SPECIFIED, PACKAGING DATA ONLY")
                data.package("localhost", 0, options)

    exit(0)


if __name__ == "__main__":
    main()

