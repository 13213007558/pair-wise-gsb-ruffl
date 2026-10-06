#!/usr/bin/ruby -Wall

require 'Bit_arith.rb'
require 'Bit_matrix.rb'
require 'Bit_vector.rb'

# Binary Reed-Muller code RM(r,m).
#
# Information coefficients are ordered by monomial degree from 0 through r;
# within each degree, variable subsets increase in bit-mask order.  Evaluation
# points increase in integer order, with x_1 in bit 0.  Bit_vector printing
# follows this library's existing convention, with bit 0 at the right.
class RM_code
	def initialize(r, m)
		unless Integer === r && Integer === m && m >= 0 && r >= 0 && r <= m
			raise ArgumentError, "RM_code requires 0 <= r <= m; got RM(#{r},#{m})."
		end

		@r = r
		@m = m
		@length = 1 << m
		@variable_universe = @length - 1
		@point_universe = (1 << @length) - 1
		@evaluation_point_vectors = (0...@length).map { |point_index|
			(0...m).map { |variable| (point_index >> variable) & 1 }
		}
		@coefficient_masks = []
		@information_labels = []
		@variable_names = (1..m).map { |variable| "x_#{variable}" }
		@monomial_masks = Array.new(@length, 0)
		@variable_masks = Array.new(m)

		@monomial_masks[0] = @point_universe
		(1...@length).each do |subset|
			variable = Bit_arith.lsb_pos(subset)
			@variable_masks[variable] ||= variable_evaluation_mask(variable)
			@monomial_masks[subset] =
				@monomial_masks[subset ^ (1 << variable)] & @variable_masks[variable]
		end

		(0..r).each do |degree|
			(0...m).to_a.combination(degree).each do |variables|
				subset = variables.inject(0) { |mask, variable| mask | (1 << variable) }
				@coefficient_masks << subset
				@information_labels << monomial_label(variables)
			end
		end

		@dimension = @coefficient_masks.length
		@generator_matrix = Bit_matrix.new(@dimension, @length)
		@coefficient_masks.each_with_index do |subset, row|
			@generator_matrix[row].bits = @monomial_masks[subset]
		end
	end
	attr_reader :r, :m, :length, :dimension, :generator_matrix,
		:coefficient_masks, :information_labels, :variable_names, :variable_masks,
		:evaluation_point_vectors

	def minimum_distance
		1 << (m - r)
	end

	def error_correction_radius
		(minimum_distance - 1) >> 1
	end

	def coordinates(point_index)
		check_point_index(point_index)
		(0...m).map { |variable| (point_index >> variable) & 1 }
	end

	def point_index(coordinates)
		unless coordinates.length == m && coordinates.all? { |bit| bit == 0 || bit == 1 }
			raise ArgumentError, "Expected #{m} binary coordinates; got #{coordinates.inspect}."
		end
		coordinates.each_with_index.inject(0) do |index, (bit, variable)|
			index | (bit << variable)
		end
	end

	def evaluation_points
		(0...length).map { |point_index| coordinates(point_index) }
	end

	def encode(information_word)
		information_bits = coerce_information_word(information_word)
		code_bits = 0
		@generator_matrix.rows.each_with_index do |row, coefficient|
			if (information_bits >> coefficient) & 1 == 1
				code_bits ^= row.bits
			end
		end
		word_from_bits(code_bits, length)
	end

	def majority_logic_decode(received_word)
		received = coerce_word(received_word, length)
		received_bits = received.bits
		residual_bits = received_bits
		decided_bits = 0
		tallies = []
		tie_count = 0

		r.downto(0) do |degree|
			coefficients_at_degree(degree).each do |coefficient|
				subset = @coefficient_masks[coefficient]
				outside = @variable_universe ^ subset
				ones = 0
				votes = 0

				each_submask(outside) do |fixed_variables|
					votes += 1
					parity = 0
					each_submask(subset) do |varying_variables|
						point_index = fixed_variables | varying_variables
						parity ^= (residual_bits >> point_index) & 1
					end
					ones += parity
				end

				decision = ones * 2 > votes ? 1 : 0
				tie_count += 1 if ones * 2 == votes
				tallies << {
					coefficient: coefficient,
					monomial: @information_labels[coefficient],
					ones: ones,
					zeros: votes - ones,
					votes: votes,
					decision: decision
				}
				if decision == 1
					decided_bits |= 1 << coefficient
					residual_bits ^= @monomial_masks[subset]
				end
			end
		end

		candidate = encode(decided_bits)
		distance = Bit_arith.ones(received_bits ^ candidate.bits)
		guaranteed = distance <= error_correction_radius
		{
			information_word: word_from_bits(decided_bits, dimension),
			codeword: candidate,
			distance: distance,
			guaranteed_recovery: guaranteed,
			status: guaranteed ? :guaranteed : :best_effort,
			tie_count: tie_count,
			majority_votes: tallies
		}
	end

	alias decode majority_logic_decode

	private

	def variable_evaluation_mask(variable)
		mask = 0
		(0...length).each do |point_index|
			mask |= 1 << point_index if (point_index >> variable) & 1 == 1
		end
		mask
	end

	def monomial_label(variables)
		return "1" if variables.empty?
		variables.map { |variable| "x_#{variable + 1}" }.join
	end

	def coefficients_at_degree(degree)
		start = (0...degree).inject(0) { |sum, index| sum + choose(m, index) }
		start...(start + choose(m, degree))
	end

	def choose(n, k)
		return 1 if k == 0 || k == n
		((n - k + 1)..n).inject(1, :*) / (1..k).inject(1, :*)
	end

	def each_submask(mask)
		submask = mask
		loop do
			yield submask
			break if submask == 0
			submask = (submask - 1) & mask
		end
	end

	def coerce_information_word(word)
		bits = coerce_word(word, dimension).bits
		if bits >= (1 << dimension)
			raise ArgumentError, "Information word has more than #{dimension} bits."
		end
		bits
	end

	def coerce_word(word, expected_length)
		if Bit_vector === word
			unless word.num_bits == expected_length
				raise ArgumentError,
					"Expected #{expected_length} bits; got #{word.num_bits}."
			end
			return word
		elsif Integer === word
			if word < 0 || word >= (1 << expected_length)
				raise ArgumentError, "Integer word is outside #{expected_length} bits."
			end
			bits = word
		elsif Array === word && word.length == expected_length &&
			word.all? { |bit| bit == 0 || bit == 1 }
			bits = word.each_with_index.inject(0) do |value, (bit, index)|
				value | (bit << index)
			end
		else
			raise ArgumentError, "Expected a #{expected_length}-bit Bit_vector, integer, or binary array."
		end
		w = Bit_vector.new(expected_length)
		w.bits = bits
		w
	end

	def word_from_bits(bits, expected_length)
		word = Bit_vector.new(expected_length)
		word.bits = bits
		word
	end

	def check_point_index(point_index)
		unless point_index >= 0 && point_index < length
			raise ArgumentError, "Point index #{point_index} outside 0...#{length}."
		end
	end
end
