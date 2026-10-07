#!/usr/bin/ruby -Wall

# Square-free polynomials over GF(2).  Monomials are represented outside
# this class by arrays or sets of variable names, with [] denoting 1.

require 'Bit_arith.rb'
require 'set'

class Bool_poly
	def initialize(terms, variables)
		variables = canonical_variables(variables)
		positions = {}
		variables.each_with_index {|name, index| positions[name] = index}
		@variables = variables
		@positions = positions

		bits = 0
		each_term(terms) do |term|
			term = canonical_term(term, positions)
			mask = 0
			term.each {|name| mask |= 1 << positions[name]}
			bits ^= 1 << mask
		end

		@bits = bits
	end

	attr_reader :bits, :variables

	def Bool_poly.zero(variables)
		from_bits(0, variables)
	end

	def Bool_poly.one(variables)
		from_bits(1, variables)
	end

	def Bool_poly.var(name, variables)
		Bool_poly.new([[name]], variables)
	end

	def Bool_poly.from_bits(bits, variables)
		poly = allocate
		variables = poly.send(:canonical_variables, variables)
		positions = {}
		variables.each_with_index {|name, index| positions[name] = index}
		poly.instance_variable_set(:@bits, bits)
		poly.instance_variable_set(:@variables, variables)
		poly.instance_variable_set(:@positions, positions)
		poly
	end

	def to_a
		terms = []
		bits = @bits
		while bits != 0
			mask = bits & -bits
			bits ^= mask
			exponent = Bit_arith.exact_log2(mask)
			terms << mask_to_term(exponent)
		end
		terms
	end

	alias terms to_a

	def term_sets
		to_a.collect {|term| Set.new(term)}
	end

	def to_s
		return '0' if zero?
		to_a.collect do |term|
			term.empty? ? '1' : term.join('*')
		end.join(' + ')
	end

	def inspect
		to_s
	end

	def ==(other)
		Bool_poly === other and @bits == other.bits and @variables == other.variables
	end

	alias eql? ==

	def hash
		[@bits, @variables].hash
	end

	def zero?
		@bits == 0
	end

	def nonzero?
		@bits != 0
	end

	def one?
		@bits == 1
	end

	def clone
		Bool_poly.from_bits(@bits, @variables)
	end

	def +(other)
		check_variables(other)
		Bool_poly.from_bits(@bits ^ other.bits, @variables)
	end

	alias - +

	def -@
		clone
	end

	def *(other)
		check_variables(other)
		Bool_poly.from_bits(boolean_bit_mul(@bits, other.bits), @variables)
	end

	def **(exponent)
		if exponent < 0
			raise "Bool_poly **: negative exponents are not allowed."
		end
		return Bool_poly.one(@variables) if exponent == 0
		clone
	end

	def contains?(name)
		@positions.has_key?(name)
	end

	def evaluate(assignment)
		evaluate_bits(assignment_value(assignment))
	end

	def substitute(assignment, new_variables=nil)
		new_variables = if new_variables.nil?
			@variables.select {|name| !assignment.has_key?(name)}
		else
			canonical_variables(new_variables)
		end

		bits = 0
		each_present_monomial do |monomial|
			factor_bits = 1
			present = true
			mask_to_term(monomial).each do |name|
				if assignment.has_key?(name)
					value = assignment[name] ? 1 : 0
					factor_bits &= value
					present = false if value == 0
				else
					index = new_variables.index(name)
					raise "Bool_poly.substitute: unknown variable #{name}." if index.nil?
					factor_bits = boolean_bit_mul(factor_bits, 1 << (1 << index))
				end
			end
			bits ^= factor_bits if present
		end
		Bool_poly.from_bits(bits, new_variables)
	end

	def leading_term(order=:grlex, eliminated=nil)
		require 'Bool_groebner.rb'
		Bool_groebner.leading_term(self, order, eliminated)
	end

	def monomial_bits
		monomials = []
		each_present_monomial {|mask| monomials << mask}
		monomials
	end

	private

	def canonical_variables(variables)
		if Set === variables
			variables = variables.to_a
		elsif !Array === variables
			variables = variables.to_a
		end
		if variables.uniq.length != variables.length
			raise "Bool_poly: variables must be distinct."
		end
		variables
	end

	def canonical_term(term, positions)
		if Set === term
			term = term.to_a
		elsif !Array === term
			term = term.to_a
		end
		term.each do |name|
			if !positions.has_key?(name)
				raise "Bool_poly: variable #{name} is not in #{@variables.inspect}."
			end
		end
		term.uniq.sort_by {|name| @positions[name]}
	end

	def each_term(terms)
		if terms.nil?
			return
		elsif terms.is_a?(Hash)
			terms.each do |term, coefficient|
				yield(term) if coefficient.to_i & 1 == 1
			end
		elsif Bool_poly === terms
			raise "Bool_poly: use Bool_poly arithmetic for Bool_poly input." if terms.variables != @variables
			terms.to_a.each {|term| yield(term)}
		else
			Array(terms).each {|term| yield(term)}
		end
	end

	def each_present_monomial
		bits = @bits
		while bits != 0
			monomial_bit = bits & -bits
			bits ^= monomial_bit
			yield(Bit_arith.exact_log2(monomial_bit))
		end
	end

	def mask_to_term(mask)
		term = []
		@variables.each_with_index do |name, index|
			term << name if (mask >> index) & 1 == 1
		end
		term
	end

	def check_variables(other)
		if !Bool_poly === other
			raise "Bool_poly: expected another Bool_poly; got #{other.class}."
		end
		if @variables != other.variables
			raise "Bool_poly: variable lists must match."
		end
	end

	def assignment_value(assignment)
		values = {}
		@variables.each do |name|
			if !assignment.has_key?(name)
				raise "Bool_poly.evaluate: missing value for #{name}."
			end
			values[name] = assignment[name] ? 1 : 0
		end
		values
	end

	def evaluate_bits(values)
		result = 0
		each_present_monomial do |monomial|
			product = 1
			mask_to_term(monomial).each {|name| product &= values[name]}
			result ^= product
		end
		result
	end

	def boolean_bit_mul(left, right)
		result = 0
		each_bit_monomial(left) do |left_monomial|
			each_bit_monomial(right) do |right_monomial|
				result ^= 1 << (left_monomial | right_monomial)
			end
		end
		result
	end

	def each_bit_monomial(bits)
		while bits != 0
			monomial_bit = bits & -bits
			bits ^= monomial_bit
			yield(Bit_arith.exact_log2(monomial_bit))
		end
	end
end
