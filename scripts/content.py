"""Shared Markdown rendering for published content and proposal preflight checks."""
import html
from pathlib import Path
import re
from urllib.parse import quote, unquote, urlsplit

import mistune
from mistune.scanner import Matcher
from public_files import is_public


SITE_ROUTE = re.compile(r'(?:case|technical-information|leaderboard)(?:[/?]|$)')
PULL_REQUEST = re.compile(r'/hodge-computer/sextics/pulls?(?:/|$)', re.I)
REPOSITORY_FILE = re.compile(r'/hodge-computer/sextics/(?:blob|tree)/', re.I)
PULL_REQUEST_TEXT = re.compile(r'\b(?:PRs?|pull requests?) ?#\d+', re.I)


def link_resolver(root, source_path, extra_files=()):
    root = Path(root).resolve()
    source_path = Path(source_path)
    source = (root / source_path).resolve()
    extra_files = {(root / path).resolve() for path in extra_files}

    def check_reference(link, url):
        # Tracked prose cites papers, the book, instances, solves, discussion
        # comments and repository files. It links within the repository; the
        # website maps those links to its own pages.
        if url.netloc.lower() in {'hodge.computer', 'www.hodge.computer'} or (
                not url.scheme and not url.path and SITE_ROUTE.match(url.fragment)):
            raise ValueError(f'{source_path}: link {link} addresses the website; '
                             'link to the repository file instead')
        if url.netloc.lower() == 'github.com' and PULL_REQUEST.match(url.path):
            raise ValueError(f'{source_path}: link {link} cites a pull request; '
                             'cite the solve, instance or book section instead')
        if url.netloc.lower() == 'github.com' and REPOSITORY_FILE.match(url.path):
            raise ValueError(f'{source_path}: link {link} addresses a repository file by URL; '
                             'use a relative path, which the checks can verify')

    def exists(path):
        return path.is_relative_to(root) and (path.is_file() or path in extra_files)

    def resolve(link):
        url = urlsplit(link)
        check_reference(link, url)
        if url.scheme or url.netloc or not url.path:
            return link
        path = unquote(url.path)
        # A leading slash selects the repository root; all other paths are
        # relative to the source document, independent of which files exist.
        target = ((root if path.startswith('/') else source.parent) / path.lstrip('/')).resolve()
        if not exists(target):
            raise ValueError(f'{source_path}: missing local link {link}')
        relative = target.relative_to(root)
        # Markdown and Lean sources link to GitHub, where they live. The website
        # maps links to instances, solutions and book chapters to its own pages
        # when it shows them (assets/routes.js). Published data and media use a
        # site URL, regardless of how the source link was written.
        base = (
            '/' if is_public(relative.as_posix()) and target.suffix not in {'.md', '.lean'}
            else 'https://github.com/hodge-computer/sextics/blob/main/'
        )
        result = base + quote(relative.as_posix())
        if url.query:
            result += '?' + url.query
        if url.fragment:
            result += '#' + url.fragment
        return result
    return resolve


def slug(text):
    return re.sub(r'[^\w\s-]', '', text.lower()).strip().replace(' ', '-')


class MathMatcher(Matcher):
    # A display equation starts a block even without a preceding blank line.
    PARAGRAPH_END = re.compile(Matcher.PARAGRAPH_END.pattern + r'|(?:\n {0,3}(?:\\\[|\$\$))')


def math_plugin(markdown):
    markdown.block.scanner_cls = MathMatcher
    markdown.block.register_rule(
        'display_math', re.compile(r' {0,3}(?:\\\[([\s\S]*?)\\\]|\$\$([\s\S]*?)\$\$)[ \t]*(?:\n|$)'),
        lambda parser, match, state: {'type': 'display_math', 'raw': (match[1] or match[2] or '').strip()})
    for rules in (markdown.block.rules, markdown.block.block_quote_rules, markdown.block.list_rules):
        rules.insert(0, 'display_math')
    markdown.inline.register_rule(
        'inline_math', r'\\\([\s\S]*?\\\)',
        lambda parser, match, state: ('inline_math', match[0][2:-2].strip()))
    for rules in (markdown.inline.rules, markdown.inline.ref_link_rules):
        rules.insert(0, 'inline_math')


class Renderer(mistune.HTMLRenderer):
    def link(self, link, text=None, title=None):
        return super().link(self.resolve_link(link), text, title)

    def heading(self, text, level):
        identifier = slug(html.unescape(re.sub('<[^>]*>', '', text)))
        return f'<h{level} id="{html.escape(identifier)}">{text}</h{level}>\n'

    def text(self, text):
        # An escaped \$ arrives as its own "$" token; any other dollar is unrendered mathematics.
        if '$' in text and text != '$':
            raise ValueError(f'{self.source_path or "Markdown"}: "{text.strip()[:60]}" contains a "$" '
                             'that is not mathematics; write inline mathematics as \\(...\\), display '
                             'mathematics as $$...$$, and a literal dollar as \\$')
        return super().text(text)

    def inline_math(self, text):
        return f'<span class="inline-math" data-math>{html.escape(text)}</span>'

    def display_math(self, text):
        return f'<div class="page-equation" data-math data-display>{html.escape(text)}</div>\n'

def render(source, *, root=None, source_path=None, extra_files=()):
    if source_path:
        cited = PULL_REQUEST_TEXT.search(source)
        if cited:
            raise ValueError(f'{source_path}: "{cited[0]}" cites a pull request; '
                             'cite the solve, instance or book section instead')
    renderer = Renderer(escape=True)
    renderer.source_path = source_path
    renderer.resolve_link = link_resolver(root, source_path, extra_files) if source_path else lambda link: link
    markdown = mistune.create_markdown(renderer=renderer, plugins=['table', 'strikethrough', math_plugin])
    return markdown(source)

