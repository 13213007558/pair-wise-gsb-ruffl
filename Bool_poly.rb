#!/usr/bin/ruby -Wall

class Bool_mono_order
	attr_reader :variables, :type, :elimination_count

	def initialize(variables, type=:lex, elimination_count=0)
		@variables = variables.collect(&:to_sym)
		if @variables.uniq.length != @variables.length
			raise "Bool_mono_order: variables must be unique."
		end

		@type = case type.to_s
		when "lex", "lexicographic" then :lex
		when "grlex", "graded_lex" then :grlex
		when "grevlex", "graded_reverse_lex" then :grevlex
		when "elim", "eliminate", "block" then :elim
		else raise "Bool_mono_order: unknown order #{type}."
		end

		@elimination_count = elimination_count.to_i
		if @type == :elim && (@elimination_count < 0 ||
			@elimination_count > @variables.length)
			raise "Bool_mono_order: invalid elimination count."
		end
	end

	def index(variable)
		@variables.index(variable.to_sym)
	end

	def eliminated?(monomial)
		@type == :elim && monomial.any? do |variable|
			index(variable) < @elimination_count
		end
	end

	def compare(this, that)
		this = this.collect(&:to_sym)
		that = that.collect(&:to_sym)
		return 0 if exponent_counts(this) == exponent_counts(that)

		if @type == :elim
			rv = compare_block(this, that)
			return rv unless rv == 0
			if this.any? {|variable| @variables[0...@elimination_count].include?(variable)}
				return compare_lex(this, that,
					@variables[0...@elimination_count] + remaining_variables)
			end
			return compare_lex(this, that, remaining_variables)
		end
		return compare_lex(this, that, @variables) if @type == :lex

		degree_difference = this.length - that.length
		return degree_difference if degree_difference != 0
		return compare_reverse_lex(this, that) if @type == :grevlex
		compare_lex(this, that, @variables)
	end

	def leading_monomial(polynomial)
		polynomial.terms.max {|a, b| compare(a, b)}
	end

	def sort_polynomials(polynomials)
		polynomials.sort do |left, right|
			compare(leading_monomial(right), leading_monomial(left))
		end
	end

	private

	def remaining_variables
		@variables[@elimination_count...@variables.length]
	end

	def compare_lex(this, that, variables)
		for variable in variables
			in_this = exponent_counts(this)[variable]
			in_that = exponent_counts(that)[variable]
			next if in_this == in_that
			return in_this > in_that ? 1 : -1
		end
		0
	end

	def compare_reverse_lex(this, that)
		for variable in @variables.reverse
			in_this = exponent_counts(this)[variable]
			in_that = exponent_counts(that)[variable]
			return -1 if in_this > in_that
			return 1 if in_this < in_that
		end
		0
	end

	def compare_block(this, that)
		eliminated = @variables[0...@elimination_count]
		this_has = this.any? {|variable| eliminated.include?(variable)}
		that_has = that.any? {|variable| eliminated.include?(variable)}
		return 0 if this_has == that_has
		(this_has ? 1 : -1)
	end

	def exponent_counts(monomial)
		counts = Hash.new(0)
		monomial.each {|variable| counts[variable] += 1}
		counts
	end
end

class Bool_poly
	def Bool_poly.with_terms(terms)
		polynomial = allocate
		polynomial.instance_variable_set(:@terms, terms)
		polynomial
	end

	def add_terms(other)
		counts = Hash.new(0)
		(@terms + other.terms).each do |term|
			counts[term] ^= 1
		end
		canonical_terms = counts.keys.select do |term|
			counts[term] == 1
		end
		Bool_poly.with_terms(canonical_terms.sort_by {|term| [term.length, term]})
	end

	attr_reader :terms

	def initialize(*args)
		if args.length == 1
			arg = args[0]
			if Bool_poly === arg
				@terms = arg.terms.map(&:dup)
			elsif String === arg
				@terms = self.class.canonical_terms(arg.split('+'))
			elsif Array === arg
				@terms = self.class.canonical_terms(arg)
			elsif Integer === arg
				@terms = arg == 1 ? [[]] : []
			else
				@terms = self.class.canonical_terms([arg])
			end
		else
			@terms = self.class.canonical_terms(args)
		end
	end

	def Bool_poly.var(variable)
		Bool_poly.new([[variable]])
	end

	def Bool_poly.field_relation(variable)
		Bool_poly.with_terms([[variable, variable], [variable]])
	end

	def Bool_poly.canonical_terms(terms)
		counts = Hash.new(0)
		for term in terms
			monomial = canonical_monomial(term)
			next if monomial.nil?
			counts[monomial] ^= 1
		end
		counts.keys.select {|monomial| counts[monomial] == 1}
	end

	def Bool_poly.canonical_monomial(term)
		return [term] if Symbol === term
		return [] if term == 1
		return nil if term == 0

		if String === term
			term = term.strip.split(/[*\s]+/)
		elsif !Array === term
			raise "Bool_poly: invalid monomial #{term.inspect}."
		end

		return [] if term.empty?
		return [] if term == ["1"]
		return nil if term == ["0"]
		unless term.all? {|variable| Symbol === variable || String === variable}
			raise "Bool_poly: monomial variables must be symbols or strings."
		end
		term.collect {|variable| variable.to_sym}.uniq.sort
	end

	def variables
		@terms.flatten.uniq
	end

	def zero?
		@terms.empty?
	end

	def one?
		@terms == [[]]
	end

	def constant?
		zero? || one?
	end

	def hash
		@terms.sort.hash
	end

	def eql?(other)
		self == other
	end

	def ==(other)
		Bool_poly === other && @terms.sort == other.terms.sort
	end
	alias :=== :==

	def <=>(other)
		sort_key <=> other.sort_key
	end

	def +(other)
		Bool_poly.new(@terms + other.terms)
	end
	alias :- :+

	def -@
		Bool_poly.new(@terms)
	end

	def *(other)
		product_terms = @terms.product(other.terms).collect do |left, right|
			left | right
		end
		Bool_poly.new(product_terms)
	end

	def **(exponent)
		if exponent < 0
			raise "Bool_poly **: negative exponents disallowed."
		end
		exponent.zero? ? Bool_poly.new(1) : self
	end

	def evaluate(assignment)
		normalized = {}
		assignment.each {|key, value| normalized[key.to_sym] = value.to_i & 1}
		satisfied_terms = @terms.count do |term|
			term.all? {|variable| normalized[variable] == 1}
		end
		satisfied_terms & 1
	end

	def leading_monomial(order)
		order.leading_monomial(self)
	end
	alias :leading_term :leading_monomial

	def to_s
		return "0" if zero?
		@terms.sort {|left, right| term_sort_key(left) <=> term_sort_key(right)}.collect do |term|
			term.empty? ? "1" : term.join("*")
		end.join(" + ")
	end
	alias :inspect :to_s

	private

	def term_sort_key(term)
		[-term.length, term]
	end

	def sort_key
		@terms.collect {|term| term_sort_key(term)}.sort
	end
end

Boolean_poly = Bool_poly
Boolean_mono_order = Bool_mono_order

class Bool_poly_system
	attr_reader :variables, :polynomials, :order

	def initialize(variables, polynomials, order=:lex, elimination_count=0)
		@variables = variables.collect(&:to_sym)
		if @variables.uniq.length != @variables.length
			raise "Bool_poly_system: variables must be unique."
		end

		@polynomials = polynomials.collect do |polynomial|
			polynomial = Bool_poly.new(polynomial) unless Bool_poly === polynomial
			unknown = polynomial.variables - @variables
			if !unknown.empty?
				raise "Bool_poly_system: unknown variables #{unknown}."
			end
			polynomial
		end
		@field_polynomials = @variables.collect do |variable|
			Bool_poly.field_relation(variable)
		end

		if Bool_mono_order === order
			if order.variables != @variables
			raise "Bool_poly_system: order variables do not match system variables."
			end
			@order = order
		elsif order.is_a?(Array)
			elimination_count = order[1].to_i if order.length > 1
			order = order[0]
			@order = Bool_mono_order.new(@variables, order, elimination_count)
		else
			@order = Bool_mono_order.new(@variables, order, elimination_count)
		end
	end

	def groebner_basis
		@order.sort_polynomials(remove_field_relations(groebner_basis_internal.values))
	end
	alias :gb :groebner_basis

	def reduced_groebner_basis
		basis = reduce_tails(groebner_basis_internal).values
		@order.sort_polynomials(remove_field_relations(basis))
	end
	alias :reduced_gb :reduced_groebner_basis
	alias :reduced_groebner_basis_for :reduced_groebner_basis

	def consistent?
		reduced_groebner_basis.any?(&:one?) == false
	end

	def eliminate(eliminated)
		eliminated = Array(eliminated).collect(&:to_sym)
		unknown = eliminated - @variables
		if !unknown.empty?
			raise "Bool_poly_system.eliminate: unknown variables #{unknown}."
		end

		ordered_variables = eliminated + (@variables - eliminated)
		system = Bool_poly_system.new(ordered_variables, @polynomials,
			:elim, eliminated.length)
		basis = system.reduced_groebner_basis
		return [Bool_poly.new(1)] if basis.any?(&:one?)
		basis.reject do |polynomial|
			system.order.eliminated?(polynomial.leading_monomial(system.order))
		end
	end

	def solutions
		return [] if !consistent?

		(0...(1 << @variables.length)).select do |bits|
			assignment = {}
			@variables.each_with_index do |variable, index|
				assignment[variable] = (bits >> index) & 1
			end
			@polynomials.all? {|polynomial| polynomial.evaluate(assignment).zero?}
		end.collect do |bits|
			assignment = {}
			@variables.each_with_index do |variable, index|
				assignment[variable] = (bits >> index) & 1
			end
			assignment
		end
	end

	private

	def groebner_basis_internal
		basis = {}
		pairs = []
		next_id = 0

		for polynomial in @field_polynomials + @polynomials
			next if polynomial.zero?
			insert_polynomial(basis, pairs, polynomial, next_id)
			next_id += 1
			if basis.one? && basis.values[0].one?
				return {next_id => basis.values[0]}
			end
		end

		while !pairs.empty?
			left_id, right_id = pairs.shift
			next unless basis.include?(left_id) && basis.include?(right_id)
			left = basis[left_id]
			right = basis[right_id]
			left_lm = left.leading_monomial(@order)
			right_lm = right.leading_monomial(@order)
			least_common_multiple = monomial_lcm(left_lm, right_lm)
			s_polynomial = multiply_by(left,
				monomial_quotient(least_common_multiple, left_lm)).add_terms(
				multiply_by(right,
				monomial_quotient(least_common_multiple, right_lm)))
			reduced = normal_form(s_polynomial, basis)
			next if reduced.zero?
			insert_polynomial(basis, pairs, reduced, next_id)
			next_id += 1
			if basis.one? && basis.values[0].one?
				return {next_id => basis.values[0]}
			end
		end

		basis
	end

	def insert_polynomial(basis, pairs, polynomial, new_id)
		reduced = normal_form(polynomial, basis)
		return if reduced.zero?

		new_lm = reduced.leading_monomial(@order)
		removed = basis.keys.select do |id|
			old_lm = basis[id].leading_monomial(@order)
			proper_divides?(new_lm, old_lm) || new_lm == old_lm
		end
		removed.each {|id| basis.delete(id)}
		basis[new_id] = reduced
		survivors = basis.keys - [new_id]
		survivors.each {|id| pairs << [id, new_id]}
	end

	def normal_form(polynomial, basis)
		reduced = polynomial
		while true
			reducible_term = reduced.terms.select do |term|
				basis.values.any? do |reducer|
					divides?(reducer.leading_monomial(@order), term)
				end
			end.max {|left, right| @order.compare(left, right)}
			break if reducible_term.nil?

			reducer = basis.values.select do |candidate|
				divides?(candidate.leading_monomial(@order), reducible_term)
			end.max do |left, right|
				@order.compare(left.leading_monomial(@order),
					right.leading_monomial(@order))
			end
			multiplier = monomial_quotient(reducible_term,
				reducer.leading_monomial(@order))
			reduced = reduced.add_terms(multiply_by(reducer, multiplier))
		end
		reduced
	end

	def multiply_by(polynomial, monomial)
		product_terms = polynomial.terms.collect do |term|
			counts = monomial_counts(term)
			monomial_counts(monomial).each do |variable, exponent|
				counts[variable] += exponent
			end
			counts_to_monomial(counts)
		end
		Bool_poly.with_terms(product_terms)
	end

	def divides?(left, right)
		left_counts = monomial_counts(left)
		right_counts = monomial_counts(right)
		left_counts.all? {|variable, exponent| right_counts[variable] >= exponent}
	end

	def proper_divides?(left, right)
		divides?(left, right) && monomial_counts(left) != monomial_counts(right)
	end

	def monomial_lcm(left, right)
		counts = monomial_counts(left)
		monomial_counts(right).each do |variable, exponent|
			counts[variable] = [counts[variable], exponent].max
		end
		counts_to_monomial(counts)
	end

	def monomial_quotient(left, right)
		counts = monomial_counts(left)
		monomial_counts(right).each do |variable, exponent|
			counts[variable] -= exponent
		end
		counts_to_monomial(counts)
	end

	def monomial_counts(monomial)
		counts = Hash.new(0)
		monomial.each {|variable| counts[variable] += 1}
		counts
	end

	def counts_to_monomial(counts)
		counts.keys.sort.collect do |variable|
			[variable] * counts[variable]
		end.flatten(1)
	end

	def remove_field_relations(polynomials)
		polynomials.reject do |polynomial|
			next false if polynomial.one?
			terms = polynomial.terms
			next false unless terms.length == 2
			linear = terms.find {|term| term.length == 1}
			squared = terms.find do |term|
				term.length == 2 && term[0] == term[1]
			end
			!linear.nil? && !squared.nil? && linear[0] == squared[0]
		end
	end

	def reduce_tails(basis_polynomials)
		active = {}
		basis_polynomials.each_value.with_index do |polynomial, id|
			active[id] = polynomial
		end
		active.keys.each do |id|
			polynomial = active.delete(id)
			reduced = normal_form(polynomial, active)
			active[id] = reduced unless reduced.zero?
		end
		active
	end
end

Boolean_poly_system = Bool_poly_system
