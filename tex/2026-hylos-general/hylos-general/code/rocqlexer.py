from pygments.lexers.theorem import CoqLexer
from pygments.token import Keyword


class RocqLexer(CoqLexer):
    name = 'Rocq'
    vernac = {'Derive', 'Abbreviation', 'Canonical'}
    tactics = {'arewrite', 'finished', 'injection'}

    def get_tokens_unprocessed(self, text):
        for i, t, v in super().get_tokens_unprocessed(text):
            if v in self.vernac:
                t = Keyword.Namespace
            elif v in self.tactics:
                t = Keyword
            yield i, t, v
