EMPTY = "epsilon"
END = "$"


class Parser:
    """Implementd from
    https://www.cs.virginia.edu/~cs415/reading/FirstFollowLL.pdf
    """

    def __init__(self, tokens, rules):
        """
        Args:
            rules (list[list[str, list[str]]])
        """
        self.__tokens = tokens
        self.__rules = rules
        self.__nonterminals = {r[0] for r in rules}
        self.__start_nonterminal = rules[0][0]

        # memoization
        self.__firsts_dict = self.__make_firsts()
        self.__follows_dict = self.__make_follows()

    def __make_firsts(self):
        firsts_dict = {}
        firsts_stack = set()

        for token in self.__tokens:
            firsts_dict[token] = self.__memoized_firsts(token, firsts_dict, firsts_stack)
            assert not firsts_stack

        for rule, _ in self.__rules:
            firsts_dict[rule] = self.__memoized_firsts(rule, firsts_dict, firsts_stack)
            assert not firsts_stack

        return firsts_dict

    def __make_follows(self):
        follows_dict = {}
        follows_stack = set()

        # Only rules are in the follows dict
        for rule, _ in self.__rules:
            follows_dict[rule] = self.__memoized_follows(rule, follows_dict, follows_stack)
            assert not follows_stack

        return follows_dict

    def is_terminal(self, symbol):
        return symbol in self.__tokens

    def firsts(self, symbol):
        return self.__firsts_dict[symbol]

    def __memoized_firsts(self, symbol, firsts_dict, firsts_stack):
        assert isinstance(symbol, basestring)

        # Already set
        if symbol in firsts_dict:
            return firsts_dict[symbol]

        firsts_set = set()

        if self.is_terminal(symbol) or symbol == EMPTY:
            firsts_set = {symbol}
        else:
            if symbol not in firsts_stack:
                firsts_stack.add(symbol)

                # Construct the firsts set for the nonterminal
                for rule, prod in self.__rules:
                    if rule == symbol:
                        # For each production that mapped to rule X

                        # Put firsts(Y1) - {e} into firsts(X)
                        firsts_set |= self.__memoized_firsts(prod[0], firsts_dict, firsts_stack) - {EMPTY}

                        # Check for epsilon in each symbol in the prod
                        all_have_empty = True
                        prev_firsts = set(firsts_set)
                        for i in xrange(len(prod) - 1):
                            if EMPTY in prev_firsts:
                                prev_firsts = self.__memoized_firsts(prod[i+1], firsts_dict, firsts_stack) - {EMPTY}
                                firsts_set |= prev_firsts
                            else:
                                all_have_empty = False

                        if all_have_empty and EMPTY in self.__memoized_firsts(prod[-1], firsts_dict, firsts_stack):
                            firsts_set.add(EMPTY)

                firsts_stack.remove(symbol)

        # Memoize for recursive calls
        firsts_dict[symbol] = firsts_set

        return firsts_set

    def follows(self, symbol):
        return self.__follows_dict[symbol]

    def __memoized_follows(self, symbol, follows_dict, follows_stack):
        assert isinstance(symbol, basestring)

        # Already in follows dict
        if symbol in follows_dict:
            return follows_dict[symbol]

        follows_set = set()

        if symbol not in follows_stack:
            follows_stack.add(symbol)

            if symbol == self.__start_nonterminal:
                follows_set.add(END)

            # Find the productions with A on the RHS
            for rule, prod in self.__rules:
                for i in xrange(len(prod)-1):
                    if prod[i] == symbol:
                        follows_set |= self.firsts(prod[i+1]) - {EMPTY}
                        if EMPTY in self.firsts(prod[i+1]):
                            follows_set |= self.__memoized_follows(rule, follows_dict, follows_stack)
                if prod[-1] == symbol:
                    follows_set |= self.__memoized_follows(rule, follows_dict, follows_stack)

            follows_dict[symbol] = follows_set
            follows_stack.remove(symbol)

        return follows_set


def test_rules():
    # From the rules_test_sec.txt
    tokens = {"b", "d", "a", "o", "z", "c"}
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
    parser = Parser(tokens, rules)

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


def test_rules2():
    # From
    # https://en.wikipedia.org/wiki/Canonical_LR_parser#FIRST_and_FOLLOW_sets
    tokens = {"(", ")", "n", "+"}
    rules = [
        ["S", ["E"]],
        ["E", ["T"]],
        ["E", ["(", "E", ")"]],
        ["T", ["n"]],
        ["T", ["+", "T"]],
        ["T", ["T", "+", "T"]],
    ]
    parser = Parser(tokens, rules)

    # firsts
    assert parser.firsts("S") == {"n", "+", "("}
    assert parser.firsts("E") == {"n", "+", "("}
    assert parser.firsts("T") == {"n", "+"}

    # follows
    assert parser.follows("S") == {END}
    assert parser.follows("E") == {END, ")"}
    assert parser.follows("T") == {END, ")", "+"}


def test_rules3():
    # From
    # http://www.montefiore.ulg.ac.be/~geurts/Cours/compil/2012/03-syntaxanalysis-2-2012-2013.pdf
    tokens = {"+", "*", "(", ")", "id"}
    rules = [
        ["E", ["E", "+", "T"]],
        ["E", ["T"]],
        ["T", ["T", "*", "F"]],
        ["T", ["F"]],
        ["F", ["(", "E", ")"]],
        ["F", ["id"]],
    ]
    parser = Parser(tokens, rules)

    # firsts
    assert parser.firsts("E") == parser.firsts("T") == parser.firsts("F") == {"id", "("}

    # follows
    assert parser.follows("E") == {"$", "+", ")"}
    assert parser.follows("T") == parser.follows("F") == {"$", "+", ")", "*"}


def test_rules4():
    # My test rules
    tokens = {"ADD", "SUB", "MUL", "DIV", "NAME", "INT"}
    rules = [
        ["module", ["expr"]],
        ["expr", ["expr", "ADD", "expr"]],
        ["expr", ["expr", "SUB", "expr"]],
        ["expr", ["expr", "MUL", "expr"]],
        ["expr", ["expr", "DIV", "expr"]],
        ["expr", ["NAME"]],
        ["expr", ["INT"]],
    ]
    parser = Parser(tokens, rules)

    # firsts
    assert parser.firsts("expr") == parser.firsts("module") == {"NAME", "INT"}

    # follows
    assert parser.follows("expr") == {"ADD", "SUB", "MUL", "DIV", END}
    assert parser.follows("module") == {END}


def test_rules5():
    # Using epsilon
    tokens = {"a"}
    rules = [
        ["S", ["X"]],
        ["X", ["a"]],
        ["X", [EMPTY]],
    ]
    parser = Parser(tokens, rules)

    # firsts
    assert parser.firsts("X") == parser.firsts("S") == {"a", EMPTY}

    # follows
    assert parser.follows("X") == {END}
    assert parser.follows("S") == {END}


test_rules()
test_rules2()
test_rules3()
test_rules4()
test_rules5()
