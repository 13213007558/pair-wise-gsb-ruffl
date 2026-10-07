#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
# ================================================================

require 'Bool_poly.rb'
require 'test/unit'

class Bool_poly_unit_test < Test::Unit::TestCase

	VARIABLES = [:x, :y, :z]

	def test_zero_one_and_terms
		zero = Bool_poly.zero(VARIABLES)
		one = Bool_poly.one(VARIABLES)
		x = Bool_poly.new([[:x]], VARIABLES)

		assert_equal([], zero.to_a)
		assert_equal([[]], one.to_a)
		assert_equal([[:x]], x.to_a)
		assert_equal([Set.new([:x])], x.term_sets)
		assert(zero.zero?)
		assert(one.one?)
		assert(!x.one?)
	end

	def test_repeated_terms_cancel_in_gf2
		poly = Bool_poly.new([[:x], [:y], [:x]], VARIABLES)
		assert_equal([[:y]], poly.to_a)

		set_poly = Bool_poly.new([Set.new([:x, :y]), Set.new([:y, :x])], VARIABLES)
		assert_equal([], set_poly.to_a)
	end

	def test_duplicate_variables_make_square_free_monomial
		poly = Bool_poly.new([[:x, :x, :y]], VARIABLES)
		assert_equal([[:x, :y]], poly.to_a)
	end

	def test_addition_is_xor
		x = Bool_poly.new([[:x]], VARIABLES)
		y = Bool_poly.new([[:y]], VARIABLES)
		assert_equal(Bool_poly.zero(VARIABLES), x + x)
		assert_equal(Bool_poly.new([[:x], [:y]], VARIABLES), x + y)
		assert_equal(x, -x)
	end

	def test_multiplication_uses_boolean_idempotence
		x = Bool_poly.new([[:x]], VARIABLES)
		x_plus_one = Bool_poly.new([[:x], []], VARIABLES)
		x_plus_y = Bool_poly.new([[:x], [:y]], VARIABLES)

		assert_equal(x, x * x)
		assert_equal(Bool_poly.new([[:x], []], VARIABLES), x_plus_one * x_plus_one)
		assert_equal(Bool_poly.new([[:y], [:x, :y]], VARIABLES), x_plus_one * x_plus_y)
	end

	def test_powers_are_idempotent
		x_plus_y = Bool_poly.new([[:x], [:y]], VARIABLES)
		assert_equal(Bool_poly.one(VARIABLES), x_plus_y ** 0)
		assert_equal(x_plus_y, x_plus_y ** 1)
		assert_equal(x_plus_y, x_plus_y ** 5)
	end

	def test_evaluation
		x_and_y = Bool_poly.new([[:x, :y]], VARIABLES)
		x_plus_y = Bool_poly.new([[:x], [:y]], VARIABLES)
		assignment = {:x => true, :y => true, :z => false}

		assert_equal(1, x_and_y.evaluate(assignment))
		assert_equal(0, x_plus_y.evaluate(assignment))
		assert_raise(RuntimeError) {x_and_y.evaluate(:x => true, :y => true)}
	end

	def test_substitution
		x_plus_y = Bool_poly.new([[:x], [:y]], VARIABLES)
		result = x_plus_y.substitute({:x => true}, [:y, :z])
		assert_equal(Bool_poly.new([[], [:y]], [:y, :z]), result)

		result = x_plus_y.substitute({:x => false}, [:y, :z])
		assert_equal(Bool_poly.new([[:y]], [:y, :z]), result)
	end

	def test_unknown_variable_is_rejected
		assert_raise(RuntimeError) {Bool_poly.new([[:w]], VARIABLES)}
	end
end
