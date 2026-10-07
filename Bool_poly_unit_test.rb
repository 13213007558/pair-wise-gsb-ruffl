#!/usr/bin/ruby -Wall

require 'Bool_poly.rb'
require 'set'
require 'test/unit'

class Bool_poly_unit_test < Test::Unit::TestCase

	def test_terms_are_explicit_variable_sets
		assert_equal([[]], Bool_poly.new(1).terms)
		assert_equal([], Bool_poly.new(0).terms)
		assert_equal([[:x]], Bool_poly.var(:x).terms)
		assert_equal([[:x, :y]], (Bool_poly.var(:x) * Bool_poly.var(:y)).terms)
		assert_equal([[:x, :y]], Bool_poly.new("x*y").terms)
		assert_equal([[], [:x], [:x, :y]], Bool_poly.new("1 + x + x*y").terms.sort)
	end

	def test_duplicate_terms_cancel_in_gf2
		x = Bool_poly.var(:x)
		y = Bool_poly.var(:y)
		assert(Bool_poly.new([[:x], [:x]]).zero?)
		assert_equal(y, x + x + y)
		assert_equal(Bool_poly.new(1), x + x + Bool_poly.new(1))
	end

	def test_idempotent_multiplication
		x = Bool_poly.var(:x)
		y = Bool_poly.var(:y)
		assert_equal(x, x * x)
		assert_equal(x, x ** 3)
		assert_equal(x * y, (x * y) * (x * y))
	end

	def test_evaluation_is_xor_not_or
		x = Bool_poly.var(:x)
		y = Bool_poly.var(:y)
		assert_equal(0, (x + y).evaluate(x: 1, y: 1))
		assert_equal(1, (x + y).evaluate(x: 1, y: 0))
		assert_equal(0, (Bool_poly.new(1) + x * y).evaluate(x: 1, y: 1))
		assert_equal(1, (Bool_poly.new(1) + x * y).evaluate(x: 0, y: 0))
	end

	def test_monomial_orders
		lex = Bool_mono_order.new([:x, :y, :z], :lex)
		grlex = Bool_mono_order.new([:x, :y, :z], :grlex)
		grevlex = Bool_mono_order.new([:x, :y, :z], :grevlex)

		assert_equal(1, lex.compare([:x], [:y, :z]))
		assert_equal(-1, grlex.compare([:x], [:y, :z]))
		assert_equal(-1, grevlex.compare([:x], [:y, :z]))
		assert_equal(-1, grlex.compare([:x, :z], [:x, :y]))
		assert_equal(-1, grevlex.compare([:x, :z], [:x, :y]))
		lex_xy = Bool_mono_order.new([:x, :y], :lex)
		assert_equal(lex_xy,
			Bool_poly_system.new([:x, :y], [], lex_xy).order)
	end

	def test_truth_table_solutions
		x = Bool_poly.var(:x)
		y = Bool_poly.var(:y)
		system = Bool_poly_system.new([:x, :y], [x + y])
		expected = [
			{x: 0, y: 0},
			{x: 1, y: 1}
		]
		assert_equal(expected, system.solutions)
		assert_equal([], Bool_poly_system.new([:x], [x, Bool_poly.new(1) + x]).solutions)
		assert_equal(4, Bool_poly_system.new([:x, :y], []).solutions.length)
		assert_equal([{}], Bool_poly_system.new([], []).solutions)
		assert_equal([], Bool_poly_system.new([], [Bool_poly.new(1)]).solutions)
	end

	def test_reduced_groebner_basis
		x = Bool_poly.var(:x)
		y = Bool_poly.var(:y)
		system = Bool_poly_system.new([:x, :y], [x + y])
		basis = system.reduced_groebner_basis

		assert_equal([x + y], basis)
		assert_reduced(basis, system.order)
		assert_equal(2, count_common_solutions(system, basis, [:x, :y]))
	end

	def test_inconsistent_system_has_unit_basis
		x = Bool_poly.var(:x)
		system = Bool_poly_system.new([:x], [x, Bool_poly.new(1) + x])
		assert_equal([Bool_poly.new(1)], system.reduced_groebner_basis)
		assert_equal(false, system.consistent?)
		assert_equal([Bool_poly.new(1)],
			Bool_poly_system.new([], [Bool_poly.new(1)]).reduced_groebner_basis)
	end

	def test_elimination
		x = Bool_poly.var(:x)
		y = Bool_poly.var(:y)
		system = Bool_poly_system.new([:x, :y], [x + y])
		assert_equal([], system.eliminate(:x))

		x1 = Bool_poly.var(:x1)
		x2 = Bool_poly.var(:x2)
		x3 = Bool_poly.var(:x3)
		majority_is_one = x1 * x2 + x1 * x3 + x2 * x3 + Bool_poly.new(1)
		system2 = Bool_poly_system.new([:x1, :x2, :x3], [majority_is_one])
		eliminated = system2.eliminate(:x1)
		assert_equal([x2 * x3 + x2 + x3 + Bool_poly.new(1)], eliminated)
		projection = [
			{x2: 1, x3: 0},
			{x2: 0, x3: 1},
			{x2: 1, x3: 1}
		]
		assert_equal(projection, solutions_for(eliminated, [:x2, :x3]))
	end

	private

	def assert_reduced(basis, order)
		leadings = basis.collect {|polynomial| polynomial.leading_monomial(order)}
		assert_equal(leadings.length, leadings.uniq.length)
		leadings.each_with_index do |leading, i|
			leadings.each_with_index do |other, j|
				next if i == j
				assert_equal(false, divides?(other, leading))
			end
		end

		basis.each do |polynomial|
			leading = polynomial.leading_monomial(order)
			polynomial.terms.each do |term|
				next if term == leading
				leadings.each do |other|
					assert_equal(false, divides?(other, term))
				end
			end
		end
	end

	def divides?(left, right)
		(Set.new(left) - Set.new(right)).empty?
	end

	def count_common_solutions(system, basis, variables)
		solutions = all_assignments(variables).select do |assignment|
			basis.all? {|polynomial| polynomial.evaluate(assignment).zero?}
		end
		assert_equal(system.solutions, solutions)
		solutions.length
	end

	def solutions_for(polynomials, variables)
		all_assignments(variables).select do |assignment|
			polynomials.all? {|polynomial| polynomial.evaluate(assignment).zero?}
		end
	end

	def all_assignments(variables)
		(0...(1 << variables.length)).collect do |bits|
			assignment = {}
			variables.each_with_index do |variable, index|
				assignment[variable] = (bits >> index) & 1
			end
			assignment
		end
	end
end
