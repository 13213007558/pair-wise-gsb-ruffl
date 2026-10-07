#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
# ================================================================

require 'Bool_groebner.rb'
require 'test/unit'

class Bool_groebner_unit_test < Test::Unit::TestCase

	VARIABLES = [:x, :y, :z]
	MONOMIALS = [
		[], [:x], [:y], [:z], [:x, :y], [:x, :z], [:y, :z], [:x, :y, :z]
	]

	def test_monomial_orders
		poly = Bool_poly.new(MONOMIALS, VARIABLES)
		assert_equal([:x, :y, :z], Bool_groebner.leading_term(poly, :lex))
		assert_equal([:x, :y, :z], Bool_groebner.leading_term(poly, :grlex))
		assert_equal([:x, :y, :z], Bool_groebner.leading_term(poly, :grevlex))

		poly = Bool_poly.new([[:x, :z], [:x, :y]], VARIABLES)
		assert_equal([:x, :y], Bool_groebner.leading_term(poly, :lex))
		assert_equal([:x, :y], Bool_groebner.leading_term(poly, :grlex))
		assert_equal([:x, :y], Bool_groebner.leading_term(poly, :grevlex))
	end

	def test_reduced_basis_for_nested_boolean_conditions
		# x = 1, x xor y = 1, and y or z.
		polynomials = [
			Bool_poly.new([[:x], []], VARIABLES),
			Bool_poly.new([[:x], [:y], []], VARIABLES),
			Bool_poly.new([[:y, :z], [:y], [:z]], VARIABLES)
		]
		basis = Bool_groebner.basis(polynomials, VARIABLES, :lex)
		expected = [
			Bool_poly.new([[:z]], VARIABLES),
			Bool_poly.new([[:y]], VARIABLES),
			Bool_poly.new([[], [:x]], VARIABLES)
		]
		assert_equal(expected, basis)
		assert_equal(
			[{:x => true, :y => false, :z => false}],
			Bool_groebner.solutions(polynomials, VARIABLES, :lex))
	end

	def test_constant_one_means_unsatisfiable
		polynomials = [
			Bool_poly.new([[:x], []], VARIABLES),
			Bool_poly.new([[:x]], VARIABLES)
		]
		basis = Bool_groebner.basis(polynomials, VARIABLES, :lex)

		assert_equal([Bool_poly.one(VARIABLES)], basis)
		assert_equal([], Bool_groebner.solutions(polynomials, VARIABLES, :lex))
	end

	def test_empty_system_has_full_truth_table
		basis = Bool_groebner.basis([], VARIABLES, :lex)
		assert_equal([], basis)
		assert_equal(8, Bool_groebner.solutions([], VARIABLES, :lex).length)

		empty_variable_basis = Bool_groebner.basis([], [], :lex)
		assert_equal([], empty_variable_basis)
		assert_equal([{}], Bool_groebner.solutions([], [], :lex))
	end

	def test_elimination
		# y = x, z = not x implies y + z = 1.
		polynomials = [
			Bool_poly.new([[:y], [:x]], VARIABLES),
			Bool_poly.new([[:z], [:x], []], VARIABLES)
		]
		basis = Bool_groebner.eliminate(polynomials, VARIABLES, [:x], :lex)
		assert_equal([Bool_poly.new([[:z], [:y], []], VARIABLES)], basis)

		block_basis = Bool_groebner.basis(polynomials, VARIABLES, [:elim, [:x]])
		assert(block_basis.any? {|poly| basis_without_x?([poly], [:x])})
	end

	def test_normal_form_uses_boolean_relations
		poly = Bool_poly.new({[:x] => 3, [:y] => 0}, VARIABLES)
		reducers = [Bool_poly.new([[:x]], VARIABLES)]
		remainder = Bool_groebner.normal_form(
			poly, reducers, VARIABLES, :grlex)
		assert_equal(Bool_poly.zero(VARIABLES), remainder)

		x_squared = Bool_groebner::Internal_poly.new(
			{[2, 0, 0] => 1, [0, 0, 0] => 1})
		field_reducers = Bool_groebner.field_polynomials(VARIABLES)
		field_remainder = Bool_groebner::Buchberger.normal_form(
			x_squared, field_reducers, VARIABLES, :grlex, nil)
		assert_equal(Bool_poly.new([[:x], []], VARIABLES), Bool_groebner.to_external(field_remainder, VARIABLES))
	end

	def test_solutions_agree_with_truth_table
		srand(1234)
		20.times do
			polynomials = random_polynomials
			[:lex, :grlex, :grevlex].each do |order|
				assert_equal(brute_force(polynomials), Bool_groebner.solutions(polynomials, VARIABLES, order))
			end
		end
	end

	def test_output_bases_are_reduced
		srand(4321)
		orders = [:lex, :grlex, :grevlex, [:elim, [:x]]]
		20.times do
			polynomials = random_polynomials
			orders.each do |order|
				basis = Bool_groebner.basis(polynomials, VARIABLES, order)
				next if basis == [Bool_poly.one(VARIABLES)]
				assert_reduced_basis(basis, order)
			end
		end
	end

	private

	def random_polynomials
		Array.new(rand(1..3)) do
			terms = MONOMIALS.select {rand(2) == 0}
			Bool_poly.new(terms, VARIABLES)
		end.reject(&:zero?)
	end

	def brute_force(polynomials)
		(0...8).inject([]) do |solutions, bits|
			assignment = {
				:x => (bits & 4) != 0,
				:y => (bits & 2) != 0,
				:z => (bits & 1) != 0
			}
			if polynomials.all? {|poly| poly.evaluate(assignment) == 0}
				solutions + [assignment]
			else
				solutions
			end
		end
	end

	def basis_without_x?(basis, eliminated)
		basis.all? {|poly| poly.to_a.all? {|term| (term & eliminated).empty?}}
	end

	def assert_reduced_basis(basis, order)
		internals = basis.collect {|poly| Bool_groebner.to_internal(poly)}
		internals.each_with_index do |poly, index|
			rest = internals[0...index] + internals[(index + 1)..-1]
			remainder = Bool_groebner::Buchberger.normal_form(
				poly, rest, VARIABLES, order, nil)
			assert_equal(poly.terms, remainder.terms)

			lead = poly.leading_exponent(VARIABLES, order, nil)
			rest.each do |other|
				other_lead = other.leading_exponent(VARIABLES, order, nil)
				divides = lead.zip(other_lead).all? {|power, divisor| power >= divisor}
				assert(!divides)
			end
		end

		with_fields = internals + Bool_groebner.field_polynomials(VARIABLES)
		internals.each_with_index do |left, left_index|
			(left_index + 1).upto(internals.length - 1) do |right_index|
				s_poly = Bool_groebner::Buchberger.s_polynomial(
					left, internals[right_index], VARIABLES, order, nil)
				remainder = Bool_groebner::Buchberger.normal_form(
					s_poly, with_fields, VARIABLES, order, nil)
				assert(remainder.zero?)
			end
		end
	end
end
