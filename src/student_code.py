import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB

        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added

        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)

        elif isinstance(fact_rule, Rule):
	    #print 'Length of Rules: ' , len(self.rules)
	    #print 'Rules:', self.rules
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)

    def kb_assert(self, statement):
        """Assert a fact or rule into the KB

        Args:
            statement (Statement): Statement we're asserting in the format produced by read.py
        """
        printv("Asserting {!r}", 0, verbose, [statement])
        self.kb_add(Fact(statement) if factq(statement) else Rule(statement))

    def kb_ask(self, statement):
        """Ask if a fact is in the KB

        Args:
            statement (Statement) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        printv("Asking {!r}", 0, verbose, [statement])
        if factq(statement):
            f = Fact(statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else False

        else:
            print "Invalid ask:", statement
            return False

    def kb_remove_dep(self, fact_rule):
	#print("placeholder")
	if isinstance(fact_rule, Fact):
		#print(" remove_dep: is Fact")
		if len(fact_rule.supported_by) == 0:
			#print(" Fact not supported")
			#print ' len supports_facts: ' , len(fact_rule.supports_facts)
			#print ' len supports_rules: ' , len(fact_rule.supports_rules)
			for f in fact_rule.supports_facts:
				#print(" Running through supports_facts")
				for fr in f.supported_by:
					#print(" f.supported_by")
					if fr[0] == fact_rule:
						f.supported_by.remove(fr)
						#print(len(f.supported_by))
				if not f.supported_by and f.asserted == False:
					#print(" call remove_dep(f) on Fact")
					self.kb_remove_dep(f)
			for r in fact_rule.supports_rules:
				#print(" Running through supports_rules")
				#print ' len of r.supported_by: ', len(r.supported_by)
				for fr in r.supported_by:
					#print(" going through r.supported_by")
					#print ' fr[1]: ', fr[1]
					#print ' fact_rule: ', fact_rule
					if fr[0] == fact_rule:
						r.supported_by.remove(fr)
						#print(" Removing supported_by Fact")
				if not r.supported_by and not r.asserted:
					#print(" call remove_dep(r) on Fact")
					self.kb_remove_dep(r)
			#print(" Removing Fact")
			self.facts.remove(fact_rule)
		else:
			return
	elif isinstance (fact_rule, Rule):
	#else:
		#print("remove_dep: is rule")
		#self.rules.remove(fact_rule)
		if len(fact_rule.supported_by) == 0:
			#print(" Rule not supported.")
			for f in fact_rule.supports_facts:
				#print(" Running through supports_facts")
				for fr in f.supported_by:
					if fr[1] == fact_rule:
						f.supported_by.remove(fr)
						#print(len(f.supported_by))
				if not f.supported_by and not f.asserted:
					#print(" call remove_dep(f) on Rule")
					self.kb_remove_dep(f)
			for r in fact_rule.supports_rules:
				#print(" Running through supports_rules")
				for fr in r.supported_by:
					if fr[1] == fact_rule:
						r.supported_by.remove(fr)
						#print(len(r.supported_by))
				if not r.supported_by and not r.asserted:
					#print(" call remove_dep(r) on Rule")
					self.kb_remove_dep(r)
			#print(" Removing Rule")
			self.rules.remove(fact_rule)	
		else:
			return
    def kb_retract(self, statement):
        """Retract a fact from the KB

        Args:
            statement (Statement) - Statement to be asked (will be converted into a Fact)

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [statement])
        ####################################################
        # Student code goes here
	if factq(statement):
		sf = Fact(statement)
		f = self._get_fact(sf)
		#for sf in self.facts:
		#	if sf.statement == Statement(statement):
		#		f = sf
		#		break
		if not f.asserted:
			if not f.supported_by:
				self.kb_remove_dep(f)
			print(" Fact not asserted: Don't run, end kb_retract")
		else:
			#print("{!f} is asserted", 0 , verbose, [f])
			if not f.supported_by:
				self.kb_remove_dep(f)
	else:
		print(" Statement not a fact: end kb_retract")		

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
	pBindings = match(fact.statement, rule.lhs[0])
	if pBindings:
		if(len(rule.lhs) == 1):
			newBinding = instantiate(rule.rhs, pBindings)
			newFact = Fact(newBinding, [[fact, rule]])
			fact.supports_facts.append(newFact)
			rule.supports_facts.append(newFact)
			kb.kb_add(newFact)
		else:
			newLHS = []
			for s in rule.lhs[1:]:
				newLHS.append(instantiate(s, pBindings))
			newRHS = instantiate(rule.rhs, pBindings)
			newRule = Rule([newLHS, newRHS], [[fact,rule]])
			fact.supports_rules.append(newRule)
			rule.supports_rules.append(newRule)
			kb.kb_add(newRule)
