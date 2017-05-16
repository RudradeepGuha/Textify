#!/usr/bin/env python

"""textify: Convert HTML into text"""
CONST_VERSION = "0.1"
CONST_AUTHORS = "Rachit Rawat, Rudradeep Guha, Johann Fernandes"
CONST_PYTHON_VERSION = "2.7"

# import required libraries
import codecs, re
import htmlentitydefs
import sys
import urllib
import HTMLParser
import urlparse
from textwrap import wrap

# Wrap long lines at position. 0 for no wrapping.
LINE_WIDTH = 78

# Put the links after each paragraph instead of at the end.
LINKS_AFTER_EACH_PARA = 1

# HTML Internal Link is linked within the same web page
# On clicking anchor link, it's referred link automatically scrolls and display on browser.
# set true to skip these links in output text
SKIP_INTERNAL_LINKS = False


# character support
def name2cp(k):
    if k == 'apos': return ord("'")
    if hasattr(htmlentitydefs, "name2codepoint"):
        return htmlentitydefs.name2codepoint[k]
    else:
        k = htmlentitydefs.entitydefs[k]
        if k.startswith("&#") and k.endswith(";"): return int(k[2:-1])  # not in latin-1
        return ord(codecs.latin_1_decode(k)[0])


# special characters in HTML
# Support decoded entities with unifiable.

unifiable = {'rsquo': "'", 'lsquo': "'", 'rdquo': '"', 'ldquo': '"',
             'copy': '(C)', 'mdash': '--', 'nbsp': ' ', 'rarr': '->', 'larr': '<-', 'middot': '*',
             'ndash': '-', 'oelig': 'oe', 'aelig': 'ae',
             'agrave': 'a', 'aacute': 'a', 'acirc': 'a', 'atilde': 'a', 'auml': 'a', 'aring': 'a',
             'egrave': 'e', 'eacute': 'e', 'ecirc': 'e', 'euml': 'e',
             'igrave': 'i', 'iacute': 'i', 'icirc': 'i', 'iuml': 'i',
             'ograve': 'o', 'oacute': 'o', 'ocirc': 'o', 'otilde': 'o', 'ouml': 'o',
             'ugrave': 'u', 'uacute': 'u', 'ucirc': 'u', 'uuml': 'u'}

unifiable_n = {}

for k in unifiable.keys():
    unifiable_n[name2cp(k)] = unifiable[k]


def charref(name):
    if name[0] in ['x', 'X']:
        c = int(name[1:], 16)
    else:
        c = int(name)

    if c in unifiable_n.keys():
        return unifiable_n[c]
    else:
        return unichr(c)


def entityref(c):
    if c in unifiable.keys():
        return unifiable[c]
    else:
        try:
            name2cp(c)
        except KeyError:
            return "&" + c
        else:
            return unichr(name2cp(c))


def replaceEntities(s):
    s = s.group(1)
    if s[0] == "#":
        return charref(s[1:])
    else:
        return entityref(s)


r_unescape = re.compile(r"&(#?[xX]?(?:[0-9a-fA-F]+|\w{1,8}));")


def unescape(s):
    return r_unescape.sub(replaceEntities, s)


def isOnlyWhite(lineString):
    """Return false if the line does not consist of whitespace characters. Else return the line"""
    for x in lineString:
        if x is not ' ' and x is not '  ':
            return x is ' '
    return lineString


def writeToStdout(text):
    """write to stdout: Encode all output as UTF-8"""
    sys.stdout.write(text.encode('utf8'))


def wrapText(text):
    """Wrap all paragraphs in the provided text."""
    # If wrap width is set 0, return
    if not LINE_WIDTH:
        return text

    wrapped_text = ''
    newlines = 0
    for para in text.split("\n"):
        if len(para) > 0:
            if para[0] is not ' ' and para[0] is not '-' and para[0] is not '*':
                for line in wrap(para, LINE_WIDTH):
                    wrapped_text += line + "\n"
                wrapped_text += "\n"
                newlines = 2
            else:
                if not isOnlyWhite(para):
                    wrapped_text += para + "\n"
                    newlines = 1
        else:
            if newlines < 2:
                wrapped_text += "\n"
                newlines += 1
    return wrapped_text


# The <h1> to <h6> tags are used to define HTML headings.
def hn(tag):
    if tag[0] == 'h' and len(tag) == 2:
        try:
            n = int(tag[1])
            if n in range(1, 10): return n
        except ValueError:
            return 0


# HTML parser class
class _textify(HTMLParser.HTMLParser):
    def __init__(self, out=None, baseurl=''):
        HTMLParser.HTMLParser.__init__(self)

        if out is None:
            self.out = self.outtextf
        else:
            self.out = out

        self.outputText = u''  # initialize output text as empty unicode string
        self.quiet = 0
        self.p_p = 0  # number of newline character to print before next output
        self.outcount = 0
        self.start = 1
        self.space = 0
        self.a = []
        self.astack = []
        self.acount = 0
        self.list = []
        self.blockquote = 0
        self.pre = 0
        self.startpre = 0
        self.lastWasNL = 0
        self.abbr_title = None  # current abbreviation definition
        self.abbr_data = None  # last inner HTML (for abbr being defined)
        self.abbr_list = {}  # stack of abbreviations to write later
        self.baseurl = baseurl

    def outtextf(self, s):
        self.outputText += s

    def returnOutputText(self):
        HTMLParser.HTMLParser.close(self)

        self.pbr()
        self.o('', 0, 'end')

        return self.outputText

    """ Overridden methods in SGMLParser"""

    def handle_charref(self, c):
        self.o(charref(c))

    def handle_entityref(self, c):
        self.o(entityref(c))

    def handle_starttag(self, tag, attrs):
        self.categorize_tag(tag, attrs, 1)

    def handle_endtag(self, tag):
        self.categorize_tag(tag, None, 0)

    def returnAttrIndex(self, attrs):
        """ returns the index of certain set of attributes (of a link) in the
            self.a list

            If the set of attributes is not found, returns None
        """
        if not attrs.has_key('href'): return None

        i = -1
        for a in self.a:
            i += 1
            match = 0

            if a.has_key('href') and a['href'] == attrs['href']:
                if a.has_key('title') or attrs.has_key('title'):
                    if (a.has_key('title') and attrs.has_key('title') and
                                a['title'] == attrs['title']):
                        match = True
                else:
                    match = True

            if match: return i

    def categorize_tag(self, tag, attrs, start):

        # Put #'s before headings where no of # is value of n in <hn>
        if hn(tag):
            self.p()
            if start: self.o(hn(tag) * "#" + ' ')

        # The <div> tag defines a division or a section in an HTML document.
        # The <p> tag defines a paragraph.
        if tag in ['p', 'div']: self.p()

        # <br> tag produces a line break in text
        if tag == "br" and start: self.o("  \n")

        # The <hr> tag defines a thematic break in an HTML page (e.g. a shift of topic).
        if tag == "hr" and start:
            self.p()
            self.o("* * *")
            self.p()

        # The <head> element is a container for all the head elements.
        # The <style> tag is used to define style information for an HTML document.
        # The <script> tag is used to define a client-side script (JavaScript).

        if tag in ["head", "style", 'script']:
            if start:
                self.quiet += 1
            else:
                self.quiet -= 1

        # The <body> tag defines the document's body.
        if tag in ["body"]:
            self.quiet = 0  # sites like 9rules.com never close <head>

        # The <blockquote> tag specifies a section that is quoted from another source.
        if tag == "blockquote":
            if start:
                self.p();
                self.o('> ', 0, 1);
                self.start = 1
                self.blockquote += 1
            else:
                self.blockquote -= 1
                self.p()

        # The <em> tag is a phrase tag. It renders as emphasized text.
        # The content of the <i> tag is usually displayed in italic.
        # The <u> tag renders as underlined text.
        if tag in ['em', 'i', 'u']: self.o("_")

        # The <strong> tag is a phrase tag. It defines important text.
        # The <b> tag specifies bold text.
        if tag in ['strong', 'b']: self.o("**")

        # The <code> tag is a phrase tag. It defines a piece of computer code.
        if tag == "code" and not self.pre: self.o('`')  # TODO: `` `this` ``

        # The <abbr> tag defines an abbreviation or an acronym, like "Mr.", "Dec.", "ASAP", "ATM".
        if tag == "abbr":
            if start:
                attrsD = {}
                for (x, y) in attrs: attrsD[x] = y
                attrs = attrsD

                self.abbr_title = None
                self.abbr_data = ''
                if attrs.has_key('title'):
                    self.abbr_title = attrs['title']
            else:
                if self.abbr_title != None:
                    self.abbr_list[self.abbr_data] = self.abbr_title
                    self.abbr_title = None
                self.abbr_data = ''

        # The <a> tag defines a hyperlink, which is used to link from one page to another.
        if tag == "a":
            if start:
                attrsD = {}
                for (x, y) in attrs: attrsD[x] = y
                attrs = attrsD
                if attrs.has_key('href') and not (SKIP_INTERNAL_LINKS and attrs['href'].startswith('#')):
                    self.astack.append(attrs)
                    self.o("[")
                else:
                    self.astack.append(None)
            else:
                if self.astack:
                    a = self.astack.pop()
                    if a:
                        i = self.returnAttrIndex(a)
                        if i is not None:
                            a = self.a[i]
                        else:
                            self.acount += 1
                            a['count'] = self.acount
                            a['outcount'] = self.outcount
                            self.a.append(a)
                        self.o("][" + `a['count']` + "]")

        # The <img> tag defines an image in an HTML page.
        if tag == "img" and start:
            attrsD = {}
            for (x, y) in attrs: attrsD[x] = y
            attrs = attrsD
            if attrs.has_key('src'):
                attrs['href'] = attrs['src']
                alt = attrs.get('alt', '')
                i = self.returnAttrIndex(attrs)
                if i is not None:
                    attrs = self.a[i]
                else:
                    self.acount += 1
                    attrs['count'] = self.acount
                    attrs['outcount'] = self.outcount
                    self.a.append(attrs)
                self.o("![")
                self.o(alt)
                self.o("][" + `attrs['count']` + "]")

        # The <dl> tag defines a description list.
        if tag == 'dl' and start: self.p()
        # The <dt> tag defines a term/name in a description list.
        if tag == 'dt' and not start: self.pbr()
        # The <dd> tag is used to describe a term/name in a description list.
        if tag == 'dd' and start: self.o('    ')
        if tag == 'dd' and not start: self.pbr()

        # The <ol> tag defines an ordered list. An ordered list can be numerical or alphabetical.
        # <ul> - unordered list
        if tag in ["ol", "ul"]:
            if start:
                self.list.append({'name': tag, 'num': 0})
            else:
                if self.list: self.list.pop()

            self.p()

        # The <li> tag defines a list item.
        if tag == 'li':
            if start:
                self.pbr()
                if self.list:
                    li = self.list[-1]
                else:
                    li = {'name': 'ul', 'num': 0}
                self.o("  " * len(self.list))
                if li['name'] == "ul":
                    self.o("* ")
                elif li['name'] == "ol":
                    li['num'] += 1
                    self.o(`li['num']` + ". ")
                self.start = 1
            else:
                self.pbr()

        # The <table> tag defines an HTML table.
        # The <tr> element defines a table row, the <th> element defines a table header, and
        # the <td> element defines a table cell.

        if tag in ["table", "tr"] and start: self.p()
        if tag == 'td': self.pbr()

        # The <pre> tag defines preformatted text.
        if tag == "pre":
            if start:
                self.startpre = 1
                self.pre = 1
            else:
                self.pre = 0
            self.p()

    def pbr(self):
        if self.p_p == 0: self.p_p = 1

    def p(self):
        self.p_p = 2

    def o(self, data, puredata=0, force=0):
        if self.abbr_data is not None: self.abbr_data += data

        if not self.quiet:
            if puredata and not self.pre:
                data = re.sub('\s+', ' ', data)
                if data and data[0] == ' ':
                    self.space = 1
                    data = data[1:]
            if not data and not force: return

            if self.startpre:
                self.startpre = 0

            bq = (">" * self.blockquote)
            if not (force and data and data[0] == ">") and self.blockquote: bq += " "

            if self.pre:
                bq += "    "
                data = data.replace("\n", "\n" + bq)

            if self.start:
                self.space = 0
                self.p_p = 0
                self.start = 0

            if force == 'end':
                # It's the end.
                self.p_p = 0
                self.out("\n")
                self.space = 0

            if self.p_p:
                self.out(('\n' + bq) * self.p_p)
                self.space = 0

            if self.space:
                if not self.lastWasNL: self.out(' ')
                self.space = 0

            if self.a and ((self.p_p == 2 and LINKS_AFTER_EACH_PARA) or force == "end"):
                if force == "end": self.out("\n")

                newa = []
                for link in self.a:
                    if self.outcount > link['outcount']:
                        self.out("   [" + `link['count']` + "]: " + urlparse.urljoin(self.baseurl, link['href']))
                        if link.has_key('title'): self.out(" (" + link['title'] + ")")
                        self.out("\n")
                    else:
                        newa.append(link)

                if self.a != newa: self.out("\n")  # Don't need an extra line when nothing was done.

                self.a = newa

            if self.abbr_list and force == "end":
                for abbr, definition in self.abbr_list.items():
                    self.out("  *[" + abbr + "]: " + definition + "\n")

            self.p_p = 0
            self.out(data)
            self.lastWasNL = data and data[-1] == '\n'
            self.outcount += 1

    def handle_data(self, data):
        if r'\/script>' in data: self.quiet -= 1
        self.o(data, 1)

    def unknown_decl(self, data):
        pass


def textify_html(html, out=writeToStdout, URL=''):
    # create HTML parser object
    x = _textify(out, URL)
    # feed html text to parser
    x.feed(html)
    return x.returnOutputText()


# Create an output text file
def writeToFile(text):
    text_file = open("Output.txt", "w")
    text_file.write(text.encode('utf-8'))
    text_file.close()

def exec_main():
    URL = ''
    arg2 = "0"
    # if a URL is passed as cmdline argument
    if sys.argv[1:]:
        arg1 = sys.argv[1]
        if sys.argv[2:]:
            arg2 = sys.argv[2]
        # if URL starts with http or https
        # use urllib to fetch HTML code
        if arg1.startswith('http://') or arg1.startswith('https://'):
            URL = arg1
            obj = urllib.urlopen(URL)
            try:
                from feedparser import _getCharacterEncoding as enc
            except ImportError:
                enc = lambda x, y: ('utf-8', 1)
            text = obj.read()
            encoding = enc(obj.headers, text)[0]
            if encoding == 'us-ascii': encoding = 'utf-8'
            html_data = text.decode(encoding)
        else:
            # use local html file
            encoding = 'utf8'
            if len(sys.argv) > 2:
                encoding = sys.argv[2]
            html_data = open(arg1, 'r').read().decode(encoding)
    else:
        # if no arg is passed
        html_data = "Usage: python textify.py (URL|file.html)"

    if (arg2 is "1"):
        writeToFile(wrapText(textify_html(html_data, None, URL)))
    else:
        writeToStdout(wrapText(textify_html(html_data, None, URL)))


if __name__ == "__main__":
    """Following block runs from cmdline using python textify.py (URL|file.html)"""
    exec_main()
