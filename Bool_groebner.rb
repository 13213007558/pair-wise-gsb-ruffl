#!/usr/bin/ruby -Wall

# Reduced Groebner bases and elimination for small Boolean polynomial
# systems over GF(2).  All displayed monomials are square-free sets of
# variable names; x_i^2 + x_i relations are used internally.

require 'Bool_poly.rb'
require 'set'

module Bool_groebner
	module_function

	def basis(polynomials, variables, order=:grlex, eliminated=nil)
		polynomials = Array(polynomials).collect {|poly| coerce_poly(poly, variables)}
		check_order(order, variables, eliminated)
		internals = polynomials.collect {|poly| to_internal(poly)}
		internals.concat(field_polynomials(variables))
		internals = Buchberger.groebner(internals, variables, order, eliminated)
		internals = strip_field_polynomials(reduced_basis(internals, variables, order, eliminated), variables)
		to_external_basis(internals, variables, order, eliminated)
	end

	def eliminate(polynomials, variables, eliminated, order=:lex)
		external_basis = basis(polynomials, variables, order, eliminated)
		eliminated = Array(eliminated)
		external_basis.select do |poly|
			poly.to_a.all? {|term| (term & eliminated).empty?}
		end
	end

	def normal_form(polynomial, polynomials, variables, order=:grlex, eliminated=nil, include_boolean_relations=true)
		polynomial = coerce_poly(polynomial, variables)
		reducers = Array(polynomials).collect {|poly| coerce_poly(poly, variables)}
		check_order(order, variables, eliminated)
		internals = reducers.collect {|poly| to_internal(poly)}
		internals.concat(field_polynomials(variables)) if include_boolean_relations
		remainder = Buchberger.normal_form(
			to_internal(polynomial), internals, variables, order, eliminated)
		to_external(remainder, variables)
	end

	def solutions(polynomials, variables, order=:lex, eliminated=nil)
		variables = Array(variables)
		external_basis = basis(polynomials, variables, order, eliminated)
		return [] if external_basis.any? {|poly| poly.one?}
		enumerate_solutions(external_basis, variables, 0, {})
	end

	def leading_term(polynomial, order=:grlex, eliminated=nil)
		internal = to_internal(coerce_poly(polynomial, polynomial.variables))
		exponent = internal.leading_exponent(polynomial.variables, order, eliminated)
		polynomial.variables.select.with_index {|_, index| exponent[index] == 1}
	end

	def coerce_poly(polynomial, variables)
		if Bool_poly === polynomial
			if polynomial.variables != Array(variables)
				raise "Bool_groebner: polynomial variable order does not match #{variables.inspect}."
			end
			polynomial
		else
			Bool_poly.new(polynomial, variables)
		end
	end

	def check_order(order, variables, eliminated)
		if Array === order
			raise "Bool_groebner: block order needs [:elim, eliminated_variables]." if order.length != 2 || order[0] != :elim
			block = Array(order[1])
			unknown = block - Array(variables)
			raise "Bool_groebner: unknown elimination variables #{unknown.inspect}." unless unknown.empty?
		elsif ![:lex, :grlex, :grevlex].include?(order)
			raise "Bool_groebner: unknown monomial order #{order.inspect}."
		end

		if !eliminated.nil? && ![:lex, :grlex, :grevlex].include?(order)
			raise "Bool_groebner: eliminated argument requires lex, grlex, or grevlex tail order."
		end
	end

	def field_polynomials(variables)
		Array(variables).each_with_index.collect do |_, index|
			exponent = Array.new(variables.length, 0)
			exponent[index] = 2
			linear = Array.new(variables.length, 0)
			linear[index] = 1
			Internal_poly.new({exponent => 1, linear => 1})
		end
	end

	def strip_field_polynomials(polynomials, variables)
		fields = Set.new(field_polynomials(variables).collect {|poly| poly.terms.keys})
		polynomials.reject do |poly|
			fields.include?(poly.terms.keys)
		end
	end

	def unit(length)
		Array.new(length, 0)
	end

	def to_internal(poly)
		terms = {}
		poly.to_a.each do |term|
			exponent = Array.new(poly.variables.length, 0)
			term.each {|name| exponent[poly.variables.index(name)] = 1}
			terms[exponent] = 1
		end
		Internal_poly.new(terms)
	end

	def to_external(internal, variables)
		terms = internal.terms.keys.collect do |exponent|
			exponent.each_with_index.inject([]) do |names, (power, index)|
				names + (power == 0 ? [] : [variables[index]])
			end
		end
		Bool_poly.new(terms, variables)
	end

	def to_external_basis(internals, variables, order=:grlex, eliminated=nil)
		external = internals.collect {|poly| to_external(poly, variables)}
		if external.any? {|poly| poly.one?}
			return [Bool_poly.one(variables)]
		end
		external.sort_by do |poly|
			exponent = to_internal(poly).leading_exponent(variables, order, eliminated)
			exponent.inject(0) {|value, power| (value << 2) | (power == 0 ? 0 : 1)}
		end
	end

	def reduced_basis(polynomials, variables, order, eliminated)
		basis = polynomials.uniq {|poly| poly.terms}.reject(&:zero?)
		minimal = []
		minimal_leads = []
		basis.each do |poly|
			lead = poly.leading_exponent(variables, order, eliminated)
			next if minimal_leads.include?(lead)
			redundant = minimal.any? do |other|
				divides?(other.leading_exponent(variables, order, eliminated), lead)
			end
			next if redundant
			removed = minimal.partition.with_index do |other, index|
				other_lead = other.leading_exponent(variables, order, eliminated)
				other_lead != lead && divides?(lead, other_lead)
			end
			removed_polynomials, minimal = removed
			minimal_leads -= removed_polynomials.collect do |other|
				other.leading_exponent(variables, order, eliminated)
			end
			minimal << poly
			minimal_leads << lead
		end

		minimal.collect do |poly|
			reducers = minimal - [poly]
			Buchberger.normal_form(poly, reducers, variables, order, eliminated)
		end.reject(&:zero?)
	end

	def divides?(exponent, divisor)
		exponent.zip(divisor).all? {|power, divisor_power| power <= divisor_power}
	end

	def enumerate_solutions(basis, variables, index, assignment)
		return [assignment] if index == variables.length

		name = variables[index]
		[0, 1].flat_map do |value|
			next_assignment = assignment.merge(name => value == 1)
			remaining_variables = variables[(index + 1)..-1]
			partial_basis = basis.collect do |poly|
				poly.substitute(next_assignment, remaining_variables)
			end
			if partial_basis.any? {|poly| poly.one?}
				[]
			else
				enumerate_solutions(basis, variables, index + 1, next_assignment)
			end
		end
	end

	def compare_exponents(left, right, variables, order=:grlex, eliminated=nil)
		if Array === order && order[0] == :elim
			elimination_set = Array(order[1])
			comparison = compare_elimination(left, right, variables, elimination_set, :lex)
			return comparison unless comparison == 0
			return compare_lex(left, right)
		end

		if !eliminated.nil?
			comparison = compare_elimination(left, right, variables, Array(eliminated), order)
			return comparison unless comparison == 0
		end

		case order
		when :lex
			compare_lex(left, right)
		when :grlex
			comparison = left.sum <=> right.sum
			return comparison unless comparison == 0
			compare_lex(left, right)
		when :grevlex
			comparison = left.sum <=> right.sum
			return comparison unless comparison == 0
			-compare_lex(left.reverse, right.reverse)
		else
			raise "Bool_groebner: unknown monomial order #{order.inspect}."
		end
	end

	def compare_lex(left, right)
		left.each_with_index do |power, index|
			comparison = power <=> right[index]
			return comparison unless comparison == 0
		end
		0
	end

	def projection(exponent, variables, names)
		names.collect {|name| exponent[variables.index(name)]}
	end

	def compare_elimination(left, right, variables, names, second_order)
		left_elim = projection(left, variables, names)
		right_elim = projection(right, variables, names)
		comparison = compare_lex(left_elim, right_elim)
		return comparison unless comparison == 0
		case second_order
		when :lex
			compare_lex(left, right)
		when :grlex
			difference = left.sum - right.sum
			return difference <=> 0 unless difference == 0
			compare_lex(left, right)
		when :grevlex
			difference = left.sum - right.sum
			return difference <=> 0 unless difference == 0
			-compare_lex(left.reverse, right.reverse)
		else
			raise "Bool_groebner: unsupported tail order #{second_order.inspect}."
		end
	end

	class Internal_poly
		attr_reader :terms

		def initialize(terms)
			@terms = terms.select {|_, coefficient| coefficient & 1 == 1}
		end

		def zero?
			@terms.empty?
		end

		def one?(variables)
			@terms.keys == [Bool_groebner.unit(variables.length)]
		end

		def leading_exponent(variables, order, eliminated)
			raise "Bool_groebner::Internal_poly: zero polynomial has no leading term." if zero?
			@terms.keys.max do |left, right|
				Bool_groebner.compare_exponents(left, right, variables, order, eliminated)
			end
		end
	end

	module Buchberger
		module_function

		def groebner(initial_basis, variables, order, eliminated)
			basis = initial_basis.reject {|poly| poly.zero?}.uniq {|poly| poly.terms}
			pairs = []
			basis.each_with_index do |_, left_index|
				(left_index + 1).upto(basis.length - 1) do |right_index|
					pairs << [left_index, right_index]
				end
			end

			while !pairs.empty?
				left_index, right_index = pairs.shift
				left = basis[left_index]
				right = basis[right_index]
				remainder = normal_form(s_polynomial(left, right, variables, order, eliminated), basis, variables, order, eliminated)
				if !remainder.zero?
					if remainder.one?(variables)
						return [Internal_poly.new({Bool_groebner.unit(variables.length) => 1})]
					end
					new_index = basis.length
					basis << remainder
					new_index.times {|index| pairs << [index, new_index]}
				end
			end
			basis
		end

		def s_polynomial(left, right, variables, order, eliminated)
			left_lead = left.leading_exponent(variables, order, eliminated)
			right_lead = right.leading_exponent(variables, order, eliminated)
			left_lcm = left_lead.zip(right_lead).collect {|a, b| [a, b].max}
			left_quotient = left_lcm.zip(left_lead).collect {|power, lead| power - lead}
			right_quotient = left_lcm.zip(right_lead).collect {|power, lead| power - lead}
			multiply_monomial(left, left_quotient) + multiply_monomial(right, right_quotient)
		end

		def normal_form(poly, reducers, variables, order, eliminated)
			remainder = Internal_poly.new(poly.terms)
			while !remainder.zero?
				lead = remainder.leading_exponent(variables, order, eliminated)
				reducer = reducers.find do |candidate|
					!candidate.zero? && divisible?(lead, candidate.leading_exponent(variables, order, eliminated))
				end
				break if reducer.nil?
				quotient = lead.zip(reducer.leading_exponent(variables, order, eliminated)).collect {|power, divisor| power - divisor}
				remainder = remainder + multiply_monomial(reducer, quotient)
			end
			remainder
		end

		def divisible?(exponent, divisor)
			exponent.zip(divisor).all? {|power, divisor_power| power >= divisor_power}
		end

		def multiply_monomial(poly, exponent_shift)
			terms = {}
			poly.terms.each do |exponent, coefficient|
				shifted = exponent.zip(exponent_shift).collect {|power, shift| power + shift}
				if terms.has_key?(shifted)
					terms.delete(shifted)
				else
					terms[shifted] = coefficient
				end
			end
			Internal_poly.new(terms)
		end
	end
end

class Bool_groebner::Internal_poly
	def +(other)
		terms = @terms.dup
		other.terms.each do |exponent, coefficient|
			if terms.has_key?(exponent)
				terms.delete(exponent)
			else
				terms[exponent] = coefficient
			end
		end
		Bool_groebner::Internal_poly.new(terms)
	end
end
