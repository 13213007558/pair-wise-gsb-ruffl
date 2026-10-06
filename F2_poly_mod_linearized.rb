#!/usr/bin/ruby -Wall

$LOAD_PATH.unshift(__dir__) unless $LOAD_PATH.include?(__dir__)

require_relative 'Bit_matrix.rb'
require_relative 'F2_poly_factor.rb'
require_relative 'F2_poly_mod.rb'

# A formal F2-linearized (q-)polynomial over K = GF(2^n):
#
#   L(X) = sum_i a_i X^(2^i),
#
# with every a_i in the same field K.  Addition is coefficientwise XOR.
# Composition is the multiplicative operation of linearized polynomials:
#
#   (A o B)(X) = sum_{i,j} a_i b_j^(2^i) X^(2^(i+j)).
#
# Ordinary polynomial multiplication is deliberately not used: it introduces
# terms such as X^3 and does not preserve this form.
#
# Formal exponents are not automatically reduced.  When evaluating the
# induced map on the fixed field K, the explicit convention is
#
#   2^i = 2^(i mod n)  for Frobenius exponents,
#
# because x^(2^n) = x for every x in K.  Thus X^(2^n) + X is a nonzero
# formal linearized polynomial, but it induces the zero map.  The formal
# zero polynomial (all coefficients zero) also induces the zero map.
class F2_poly_mod_linearized
	@@irreducible_moduli = {}

	def initialize(coefficients, modulus, reduce = false)
		@modulus = F2_poly_mod_linearized.coerce_modulus(modulus)
		@degree = @modulus.degree
		@coefficients = {}

		case coefficients
		when Array
			coefficients.each_with_index do |coefficient, index|
				set_coefficient(index, coefficient)
			end
		when Hash
			coefficients.each do |index, coefficient|
				set_coefficient(index, coefficient)
			end
		else
			raise "F2_poly_mod_linearized: coefficients must be an Array or Hash."
		end

		if reduce
			reduced = self.class.new({}, @modulus, false)
			@coefficients.each do |index, coefficient|
				reduced.add_coefficient(index % @degree, coefficient)
			end
			@coefficients = reduced.coefficient_hash
		end
	end

	attr_reader :modulus, :degree

	def self.coerce_modulus(modulus)
		if F2_poly === modulus
			field_modulus = modulus
		elsif F2_poly_mod === modulus
			field_modulus = modulus.modulus
		else
			field_modulus = F2_poly.new(modulus)
		end

		@@irreducible_moduli[field_modulus.bits] ||= F2_poly_factor.irr?(field_modulus)
		unless @@irreducible_moduli[field_modulus.bits]
			raise "F2_poly_mod_linearized: #{field_modulus} is not irreducible; coefficients must lie in one binary extension field."
		end
		field_modulus
	end

	def self.zero(modulus)
		new({}, modulus, false)
	end

	def self.x(modulus)
		new([F2_poly_mod.new(1, coerce_modulus(modulus))], modulus, false)
	end

	# The nonzero formal polynomial X^(2^n) + X, whose map is zero on K.
	def self.field_polynomial(modulus)
		field_modulus = coerce_modulus(modulus)
		one = F2_poly_mod.new(1, field_modulus)
		new({0 => one, field_modulus.degree => one}, field_modulus, false)
	end

	def self.from_subspace_basis(basis, modulus = nil)
		elements = basis.collect do |element|
			if F2_poly_mod === element
				element
			else
				raise "F2_poly_mod_linearized.from_subspace_basis: modulus is required for non-field elements." if modulus.nil?
				F2_poly_mod.new(element, coerce_modulus(modulus))
			end
		end

		if elements.empty?
			raise "F2_poly_mod_linearized.from_subspace_basis: modulus is required for an empty basis." if modulus.nil?
			return x(modulus)
		end

		field_modulus = elements.first.modulus
		elements.each do |element|
			unless element.modulus == field_modulus
				raise "F2_poly_mod_linearized.from_subspace_basis: basis elements have different moduli."
			end
		end
		coerce_modulus(field_modulus)

		n = field_modulus.degree
		d = elements.length
		if d > n
			raise "F2_poly_mod_linearized.from_subspace_basis: more than #{n} basis vectors were supplied."
		end

		basis_matrix = Bit_matrix.new(d, n)
		elements.each_with_index do |element, row|
			basis_matrix[row].bits = element.residue.bits
		end
		if basis_matrix.rank != d
			raise "F2_poly_mod_linearized.from_subspace_basis: basis is not linearly independent over F2."
		end

		return field_polynomial(field_modulus) if d == n

		rows = elements.collect do |element|
			powers = []
			power = element
			(d + 1).times do
				powers << power
				power = power * power
			end
			powers
		end

		# Solve v_j^(2^d) = sum_k c_k v_j^(2^k) over K using Gauss-Jordan
		# elimination.  The Moore matrix is nonsingular for an F2-independent
		# basis.
		for column in 0...d
			pivot_row = column
			while pivot_row < d && rows[pivot_row][column].zero?
				pivot_row += 1
			end
			if pivot_row == d
				raise "F2_poly_mod_linearized.from_subspace_basis: singular Moore matrix."
			end
			rows[column], rows[pivot_row] = rows[pivot_row], rows[column]

			pivot_factor = rows[column][column].recip
			rows[column] = rows[column].collect {|value| pivot_factor * value}

			rows.each_with_index do |row, row_index|
				next if row_index == column
				factor = row[column]
				next if factor.zero?
				rows[row_index] = row.each_with_index.collect do |value, value_index|
					value + factor * rows[column][value_index]
				end
			end
		end

		coefficients = {}
		rows.each_with_index do |row, column|
			coefficients[column] = row[d]
		end
		coefficients[d] = F2_poly_mod.new(1, field_modulus)
		new(coefficients, field_modulus, false)
	end

	def coefficient_hash
		@coefficients.dup
	end

	def coefficients
		max_index = @coefficients.keys.max || -1
		(0..max_index).collect do |index|
			coefficient(index)
		end
	end

	def coefficient(index)
		@coefficients.fetch(index, F2_poly_mod.new(0, @modulus))
	end

	alias [] coefficient

	def q_degree
		@coefficients.keys.max || -1
	end

	def zero?
		@coefficients.empty?
	end

	alias formal_zero? zero?

	def zero_map?
		reduced_form.zero?
	end

	def reduced?
		!@coefficients.keys.any? {|index| index >= @degree}
	end

	def reduced_form
		self.class.new(coefficient_hash, @modulus, true)
	end

	def ==(other)
		return false unless self.class === other
		@modulus == other.modulus && coefficient_hash == other.coefficient_hash
	end

	alias eql? ==

	def hash
		[@modulus.bits, @coefficients].hash
	end

	def +(other)
		check_same_field(other, "+")
		sum = self.class.new({}, @modulus, false)
		@coefficients.each {|index, value| sum.add_coefficient(index, value)}
		other.coefficient_hash.each {|index, value| sum.add_coefficient(index, value)}
		sum
	end

	def -(other)
		self + other
	end

	def -@
		self
	end

	# Linearized-polynomial composition, not ordinary polynomial product.
	def compose(other, reduce = false)
		check_same_field(other, "composition")
		composition = self.class.new({}, @modulus, false)

		@coefficients.each do |left_index, left_coefficient|
			other.coefficient_hash.each do |right_index, right_coefficient|
				twisted = left_coefficient * frobenius(right_coefficient, left_index)
				composition.add_coefficient(left_index + right_index, twisted)
			end
		end

		reduce ? composition.reduced_form : composition
	end

	alias * compose

	def evaluate(element)
		x = coerce_element(element)
		frobenius_powers = Array.new(@degree)
		power = x
		@degree.times do |index|
			frobenius_powers[index] = power
			power = power * power
		end

		result = F2_poly_mod.new(0, @modulus)
		@coefficients.each do |index, coefficient|
			result = result + coefficient * frobenius_powers[index % @degree]
		end
		result
	end

	alias call evaluate

	def bit_matrix
		matrix = Bit_matrix.new(@degree, @degree)
		@degree.times do |input_bit|
			element = F2_poly_mod.new(F2_poly.new(1 << input_bit), @modulus)
			image = evaluate(element)
			@degree.times do |output_bit|
				matrix[output_bit][input_bit] = image.residue[output_bit]
			end
		end
		matrix
	end

	def kernel_bit_basis
		bit_matrix.kernel_basis
	end

	def kernel_basis
		basis = kernel_bit_basis
		return [] if basis.nil?
		bit_rows_to_elements(basis)
	end

	def kernel_dimension
		@degree - bit_matrix.rank
	end

	def image_bit_basis
		columns = Bit_matrix.new(@degree, @degree)
		matrix = bit_matrix
		@degree.times do |row|
			@degree.times do |column|
				columns[column][row] = matrix[row][column]
			end
		end
		columns.row_echelon_form
		basis_rows = columns.rows.select {|row| row.bits != 0}
		return nil if basis_rows.empty?

		basis = Bit_matrix.new(basis_rows.length, @degree)
		basis_rows.each_with_index do |row, index|
			basis[index].bits = row.bits
		end
		basis
	end

	def image_basis
		basis = image_bit_basis
		return [] if basis.nil?
		bit_rows_to_elements(basis)
	end

	def image_dimension
		bit_matrix.rank
	end

	def to_s
		return "0" if zero?
		@coefficients.keys.sort.reverse.collect do |index|
			coefficient = @coefficients[index]
			term = case index
				when 0 then "x"
				when 1 then "x^2"
				else "x^(2^#{index})"
			end
			coefficient.one? ? term : "(#{coefficient})*#{term}"
		end.join(" + ")
	end

	def inspect
		"#{to_s} mod #{@modulus.inspect}"
	end

	def add_coefficient(index, value)
		raise "F2_poly_mod_linearized: Frobenius index must be nonnegative." unless Integer === index && index >= 0
		coefficient = if F2_poly_mod === value
			value
		else
			F2_poly_mod.new(value, @modulus)
		end
		if coefficient.modulus != @modulus
			raise "F2_poly_mod_linearized: all coefficients must use the same field modulus."
		end

		updated = coefficient(index) + coefficient
		if updated.zero?
			@coefficients.delete(index)
		else
			@coefficients[index] = updated
		end
	end

	private

	def set_coefficient(index, value)
		return if value.nil?
		add_coefficient(index, value)
	end

	def frobenius(element, index)
		element ** (1 << (index % @degree))
	end

	def check_same_field(other, operation)
		unless self.class === other && other.modulus == @modulus
			raise "F2_poly_mod_linearized #{operation}: operands must use the same binary extension field."
		end
	end

	def coerce_element(element)
		if F2_poly_mod === element
			unless element.modulus == @modulus
				raise "F2_poly_mod_linearized: element does not belong to the polynomial's field."
			end
			element
		else
			F2_poly_mod.new(element, @modulus)
		end
	end

	def bit_rows_to_elements(basis)
		basis.rows.collect do |row|
			F2_poly_mod.new(F2_poly.new(row.bits), @modulus)
		end
	end
end
