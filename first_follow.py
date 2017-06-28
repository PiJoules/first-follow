EMPTY = "epsilon"
END = "$"


class Parser:
    """Implementd from
    https://www.cs.virginia.edu/~cs415/reading/FirstFollowLL.pdf
    """

    def __init__(self, rules):
        """
        Args:
            rules (list[list[str, list[str]]])
        """
        self.__rules = rules
        self.__nonterminals = {r[0] for r in rules}
        self.__start_nonterminal = rules[0][0]

        # for keeping track of recusive calls
        self.__firsts_stack = set()
        self.__follows_stack = set()

        # memoization
        self.__firsts_dict = {}
        self.__follows_dict = {}

    def firsts_stack(self):
        return self.__firsts_stack

    def follows_stack(self):
        return self.__follows_stack

    def is_terminal(self, symbol):
        return not self.is_non_terminal(symbol)

    def is_non_terminal(self, symbol):
        return symbol in self.__nonterminals

    def __construct_nonterminal_firsts(self, symbol):
        assert self.is_non_terminal(symbol)

        firsts_set = set()
        for rule, prod in self.__rules:
            if rule == symbol:
                # For each production that mapped to rule X

                # Put firsts(Y1) - {e} into firsts(X)
                firsts_set |= self.firsts(prod[0]) - {EMPTY}

                # Check for epsilon in each symbol in the prod
                all_have_empty = True
                for i in xrange(len(prod) - 1):
                    if EMPTY in self.firsts(prod[i]):
                        firsts_set |= self.firsts(prod[i+1]) - {EMPTY}
                    else:
                        all_have_empty = False
                if all_have_empty and EMPTY in self.firsts(prod[-1]):
                    firsts_set.add(EMPTY)

        return firsts_set

    def firsts(self, symbol):
        assert isinstance(symbol, basestring)

        if symbol in self.__firsts_dict:
            return self.__firsts_dict[symbol]

        if self.is_terminal(symbol) or symbol == EMPTY:
            self.__firsts_dict[symbol] = {symbol}
            return self.__firsts_dict[symbol]
        else:
            if symbol not in self.__firsts_stack:
                self.__firsts_stack.add(symbol)
                firsts = self.__construct_nonterminal_firsts(symbol)
                self.__firsts_dict[symbol] = firsts
                self.__firsts_stack.remove(symbol)
                return self.__firsts_dict[symbol]
            else:
                return set()

    def follows(self, symbol):
        assert isinstance(symbol, basestring)

        if symbol in self.__follows_dict:
            return self.__follows_dict[symbol]

        if symbol in self.__follows_stack:
            return set()

        self.__follows_stack.add(symbol)

        follows_set = set()
        if symbol == self.__start_nonterminal:
            follows_set.add(END)

        # Find the productions with A on the RHS
        for rule, prod in self.__rules:
            for i in xrange(len(prod)-1):
                if prod[i] == symbol:
                    follows_set |= self.firsts(prod[i+1]) - {EMPTY}
                    if EMPTY in self.firsts(prod[i+1]):
                        follows_set |= self.follows(rule)
            if prod[-1] == symbol:
                follows_set |= self.follows(rule)

        self.__follows_dict[symbol] = follows_set
        self.__follows_stack.remove(symbol)

        return follows_set


def test_rules():
    # From the rules_test_sec.txt
    rules = [
        ["S", ["B", "b"]],
        ["S", ["C", "d"]],
        ["B", ["a", "B"]],
        ["B", ["o"]],
        ["B", ["D", "a"]],
        ["D", ["z"]],
        ["C", ["c", "C"]],
        ["C", ["o"]],
    ]
    parser = Parser(rules)

    # firsts
    assert parser.firsts("S") == {"a", "o", "z", "c"}
    assert parser.firsts("B") == {"a", "o", "z"}
    assert parser.firsts("D") == {"z"}
    assert parser.firsts("C") == {"o", "c"}

    # follows
    assert parser.follows("S") == {END}
    assert parser.follows("B") == {"b"}
    assert parser.follows("C") == {"d"}
    assert parser.follows("D") == {"a"}

    # Empty stacks
    assert not parser.firsts_stack()
    assert not parser.follows_stack()


def test_rules2():
    # From
    # https://en.wikipedia.org/wiki/Canonical_LR_parser#FIRST_and_FOLLOW_sets
    rules = [
        ["S", ["E"]],
        ["E", ["T"]],
        ["E", ["(", "E", ")"]],
        ["T", ["n"]],
        ["T", ["+", "T"]],
        ["T", ["T", "+", "T"]],
    ]
    parser = Parser(rules)

    # firsts
    assert parser.firsts("S") == {"n", "+", "("}
    assert parser.firsts("E") == {"n", "+", "("}
    assert parser.firsts("T") == {"n", "+"}

    # follows
    assert parser.follows("S") == {END}
    assert parser.follows("E") == {END, ")"}
    assert parser.follows("T") == {END, ")", "+"}

    # Empty stacks
    assert not parser.firsts_stack()
    assert not parser.follows_stack()


def test_rules3():
    # From
    # http://www.montefiore.ulg.ac.be/~geurts/Cours/compil/2012/03-syntaxanalysis-2-2012-2013.pdf
    rules = [
        ["E", ["E", "+", "T"]],
        ["E", ["T"]],
        ["T", ["T", "*", "F"]],
        ["T", ["F"]],
        ["F", ["(", "E", ")"]],
        ["F", ["id"]],
    ]
    parser = Parser(rules)

    # firsts
    assert parser.firsts("E") == parser.firsts("T") == parser.firsts("F") == {"id", "("}

    # follows
    assert parser.follows("E") == {"$", "+", ")"}
    assert parser.follows("T") == parser.follows("F") == {"$", "+", ")", "*"}

    # Empty stacks
    assert not parser.firsts_stack()
    assert not parser.follows_stack()


def test_rules4():
    # My test rules
    rules = [
        ["module", ["expr"]],
        ["expr", ["expr", "ADD", "expr"]],
        ["expr", ["expr", "SUB", "expr"]],
        ["expr", ["expr", "MUL", "expr"]],
        ["expr", ["expr", "DIV", "expr"]],
        ["expr", ["NAME"]],
        ["expr", ["INT"]],
    ]
    parser = Parser(rules)

    # firsts
    assert parser.firsts("expr") == parser.firsts("module") == {"NAME", "INT"}

    # follows
    assert parser.follows("expr") == {"ADD", "SUB", "MUL", "DIV", END}
    assert parser.follows("module") == {END}

    # Empty stacks
    assert not parser.firsts_stack()
    assert not parser.follows_stack()


def test_rules5():
    # Using epsilon
    rules = [
        ["S", ["X"]],
        ["X", ["a"]],
        ["X", [EMPTY]],
    ]
    parser = Parser(rules)

    # firsts
    assert parser.firsts("X") == parser.firsts("S") == {"a", EMPTY}

    # follows
    assert parser.follows("X") == {END}
    assert parser.follows("S") == {END}

    # Empty stacks
    assert not parser.firsts_stack()
    assert not parser.follows_stack()


test_rules()
test_rules2()
test_rules3()
test_rules4()
test_rules5()
