#!/usr/bin/ruby -Wall

require 'RM_code.rb'
require 'test/unit'

class RM_codeUnitTest < Test::Unit::TestCase

	def test_public_order_and_generator_matrix
		code = RM_code.new(1, 2)
		Bit_matrix.set_binary_output

		assert_equal(["1", "x_1", "x_2"], code.information_labels)
		assert_equal([0, 1, 2], code.coefficient_masks)
		assert_equal(["x_1", "x_2"], code.variable_names)
		assert_equal([[0, 0], [1, 0], [0, 1], [1, 1]],
			code.evaluation_point_vectors)
		assert_equal(0, code.point_index([0, 0]))
		assert_equal(1, code.point_index([1, 0]))
		assert_equal(2, code.point_index([0, 1]))
		assert_equal(3, code.point_index([1, 1]))
		assert_equal("1111\n1010\n1100\n", code.generator_matrix.to_s)
		assert_equal([10, 12], code.variable_masks)
	end

	def test_parameters_and_minimum_distance
		assert_equal([4, 3, 0], parameters_for(RM_code.new(1, 2)))
		assert_equal([2, 1, 0], parameters_for(RM_code.new(0, 1)))
		assert_equal([16, 16, 0], parameters_for(RM_code.new(4, 4)))
		assert_equal([8, 7, 0], parameters_for(RM_code.new(2, 3)))
		assert_raise(ArgumentError) { RM_code.new(-1, 2) }
		assert_raise(ArgumentError) { RM_code.new(3, 2) }
	end

	def test_small_codes_enumerate_all_information_words
		(0..3).each do |m|
			(0..m).each do |r|
				code = RM_code.new(r, m)
				(0...(1 << code.dimension)).each do |information_bits|
					codeword = code.encode(information_bits)
					assert_equal(code.length, codeword.num_bits)
					assert_equal(direct_evaluation(code, information_bits),
						codeword.bits)
					result = code.decode(codeword)
					assert_equal(information_bits, result[:information_word].bits)
					assert_equal(0, result[:distance])
					assert(result[:guaranteed_recovery])
					assert_equal(:guaranteed, result[:status])
				end
			end
		end
	end

	def test_all_errors_within_radius_for_small_codes
		small_codes do |code|
			(0...(1 << code.dimension)).each do |information_bits|
				codeword = code.encode(information_bits).bits
				each_error_pattern(code.length, code.error_correction_radius) do |error|
					received = codeword ^ error
					result = code.decode(received)
					error_weight = Bit_arith.ones(error)

					assert_equal(information_bits, result[:information_word].bits)
					assert_equal(error_weight, result[:distance])
					assert(result[:guaranteed_recovery])
					assert_equal(:guaranteed, result[:status])
				end
			end
		end
	end

	def test_boundary_errors_for_larger_small_code
		code = RM_code.new(1, 4)
		assert_equal(3, code.error_correction_radius)
		(0...(1 << code.dimension)).each do |information_bits|
			codeword = code.encode(information_bits).bits
			(0...code.length).to_a.combination(3).each do |positions|
				error = positions.inject(0) { |bits, position| bits | (1 << position) }
				result = code.decode(codeword ^ error)
				assert_equal(information_bits, result[:information_word].bits)
				assert_equal(3, result[:distance])
				assert(result[:guaranteed_recovery])
			end
		end
	end

	def test_errors_outside_radius_are_best_effort
		code = RM_code.new(0, 2)
		assert_equal(1, code.error_correction_radius)
		information_bits = 1
		codeword = code.encode(information_bits).bits
		received = codeword ^ 0b0110
		result = code.decode(received)

		assert(!result[:guaranteed_recovery])
		assert_equal(:best_effort, result[:status])
		assert_equal(2, result[:distance])
		assert(result[:tie_count] > 0)
		assert_equal(0, result[:codeword].bits)
	end

	def test_majority_votes_use_degree_order
		code = RM_code.new(2, 3)
		result = code.decode(0)
		degrees = result[:majority_votes].map do |vote|
			Bit_arith.ones(code.coefficient_masks[vote[:coefficient]])
		end
		assert_equal([2, 2, 2, 1, 1, 1, 0], degrees)
		assert_equal([2, 2, 2, 4, 4, 4, 8],
			result[:majority_votes].map { |vote| vote[:votes] })
	end

	def test_input_forms
		code = RM_code.new(1, 2)
		assert_equal(15, code.encode([1, 0, 0]).bits)
		assert_equal(10, code.encode([0, 1, 0]).bits)
		vector = Bit_vector.new(3)
		vector.bits = 4
		assert_equal(12, code.encode(vector).bits)
		codeword = code.encode([0, 1, 0])
		assert_equal(2, code.decode(codeword)[:information_word].bits)
		assert_raise(ArgumentError) { code.encode([1, 0]) }
		assert_raise(ArgumentError) { code.encode(8) }
	end

	private

	def parameters_for(code)
		[code.length, code.dimension, code.error_correction_radius]
	end

	def small_codes
		(0..3).each do |m|
			(0..m).each do |r|
				yield RM_code.new(r, m)
			end
		end
	end

	def each_error_pattern(length, weight)
		(0..weight).each do |current_weight|
			(0...length).to_a.combination(current_weight) do |positions|
				error = positions.inject(0) { |bits, position| bits | (1 << position) }
				yield error
			end
		end
	end

	def direct_evaluation(code, information_bits)
		code.evaluation_point_vectors.each_with_index.inject(0) do
			|code_bits, (point, point_index)|
			value = code.information_labels.each_with_index.inject(0) do
				|sum, (_label, coefficient)|
				next(sum) if (information_bits >> coefficient) & 1 == 0
				subset = code.coefficient_masks[coefficient]
				monomial_value = point.each_with_index.all? do |bit, variable|
					(((subset >> variable) & 1) == 0) || bit == 1
				end
				sum ^ (monomial_value ? 1 : 0)
			end
			code_bits | (value << point_index)
		end
	end
end
