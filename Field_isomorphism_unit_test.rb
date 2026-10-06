#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
#
# Tests for Field_isomorphism.
#
# Why the isomorphism is not unique: an isomorphism
# F_2[x]/(p1) -> F_2[x]/(p2) is determined by the image of the
# source generator x, which may be any root of p1 in the target
# field.  An irreducible p1 of degree m has exactly m roots in
# F_{2^m} -- a single Frobenius orbit beta, beta^2, ...,
# beta^{2^{m-1}} -- so there are exactly m distinct isomorphisms,
# differing by the m automorphisms of the target field.  The tests
# below enumerate every root, check that each one yields a valid
# isomorphism, and check that the roots are permuted by squaring.
# ================================================================

require 'Field_isomorphism.rb'
require 'test/unit'

class Field_isomorphism_unit_test < Test::Unit::TestCase

	# Irreducible moduli over F_2.
	P3A = F2_poly.new(0xb)  # x^3 + x + 1
	P3B = F2_poly.new(0xd)  # x^3 + x^2 + 1
	P4A = F2_poly.new(0x13) # x^4 + x + 1
	P4B = F2_poly.new(0x19) # x^4 + x^3 + 1
	P4C = F2_poly.new(0x1f) # x^4 + x^3 + x^2 + x + 1

	DEGREE_3_IRRS = [P3A, P3B]
	DEGREE_4_IRRS = [P4A, P4B, P4C]

	# ------------------------------------------------------------
	def test_rejects_degree_mismatch
		assert_raise(ArgumentError) { Field_isomorphism.new(P3A, P4A) }
		assert_raise(ArgumentError) { Field_isomorphism.new(P4A, P3A) }
		assert_raise(ArgumentError) { Field_isomorphism.new(3, P3A) }
	end

	def test_rejects_reducible_modulus
		# 0xc = x^3 + x^2 = x^2 (x + 1) is reducible.
		assert_raise(ArgumentError) { Field_isomorphism.new(0xc, P3A) }
		assert_raise(ArgumentError) { Field_isomorphism.new(P3A, 0xc) }
		# 0x1c = x^2 (x^2 + x + 1) is reducible, on both sides at once.
		assert_raise(ArgumentError) { Field_isomorphism.new(0x1c, 0x1c) }
		# Constants are not fields' moduli.
		assert_raise(ArgumentError) { Field_isomorphism.new(1, 1) }
	end

	def test_rejects_non_root_image
		# x itself is not a root of x^3+x+1 modulo x^3+x^2+1:
		# x^3+x+1 = (x^2+1)+x+1 = x^2+x (mod 0xd), which is nonzero.
		assert_raise(ArgumentError) { Field_isomorphism.new(P3A, P3B, 2) }
		# 0 and 1 are never roots of an irreducible of degree > 1.
		assert_raise(ArgumentError) { Field_isomorphism.new(P3A, P3B, 0) }
		assert_raise(ArgumentError) { Field_isomorphism.new(P3A, P3B, 1) }
	end

	def test_explicit_image
		# x+1 is a root of x^3+x+1 modulo x^3+x^2+1.
		iso = Field_isomorphism.new(P3A, P3B, 3)
		assert_equal(F2_poly.new(3), iso.image_of_generator)
		assert_equal(F2_poly_mod.new(3, P3B),
			iso.convert(F2_poly_mod.new(2, P3A)))
		assert_match(/explicit/, iso.rationale)
		assert_match(/3/, iso.rationale)
	end

	def test_auto_selection_is_stable_and_reports_rationale
		iso1 = Field_isomorphism.new(P3A, P3B)
		iso2 = Field_isomorphism.new(P3A, P3B)
		# Stable: same moduli always give the same image.
		assert_equal(iso1.image_of_generator, iso2.image_of_generator)
		# The roots of x^3+x+1 mod x^3+x^2+1 are x+1, x^2+1, x^2+x;
		# the lexically lowest is x+1 (bit pattern 3).
		assert_equal([3, 5, 6].collect{|b| F2_poly.new(b)}, iso1.roots)
		assert_equal(F2_poly.new(3), iso1.image_of_generator)
		assert_equal(iso1.roots[0], iso1.image_of_generator)
		# The rationale records the rule and the choice made.
		assert_match(/auto/, iso1.rationale)
		assert_match(/lexically lowest/, iso1.rationale)
		assert_match(/3 root/, iso1.rationale)
	end

	def test_bit_patterns_cannot_be_copied_directly
		# The image of the source generator is not x itself, so a
		# naive bit-pattern copy is not the isomorphism.  Concretely,
		# x^3 = x+1 (mod 0xb) but x^3 = x^2+1 (mod 0xd): copying the
		# source bits of x^3 across gives the wrong target element.
		x_src = F2_poly_mod.new(2, P3A)
		naive = F2_poly_mod.new((x_src * x_src * x_src).residue.bits, P3B)
		x_tgt = F2_poly_mod.new(2, P3B)
		assert_not_equal(naive, x_tgt * x_tgt * x_tgt)
		# The real isomorphism instead sends x to x+1 here.
		iso = Field_isomorphism.new(P3A, P3B)
		assert_not_equal(F2_poly.new(2), iso.image_of_generator)
		assert_equal(iso.convert(x_src) * iso.convert(x_src) * iso.convert(x_src),
			iso.convert(x_src * x_src * x_src))
	end

	def test_same_modulus_auto_is_identity
		# With p1 == p2 the lexically lowest root is x itself, so the
		# auto rule yields the identity map.
		iso = Field_isomorphism.new(P4A, P4A)
		assert_equal(F2_poly.new(2), iso.image_of_generator)
		F2_poly_mod.elements_for_modulus(P4A).each do |a|
			assert_equal(a, iso.convert(a))
		end
	end

	def test_convert_argument_handling
		iso = Field_isomorphism.new(P3A, P3B)
		# Accepts F2_poly_mod, F2_poly, and integer residues.
		assert_equal(iso.convert(5), iso.convert(F2_poly.new(5)))
		assert_equal(iso.convert(5), iso.convert(F2_poly_mod.new(5, P3A)))
		# Residues are reduced mod the source modulus first.
		assert_equal(iso.convert(6), iso.convert(2 + 0xb))
		# Elements of the wrong field are rejected.
		assert_raise(ArgumentError) { iso.convert(F2_poly_mod.new(1, P3B)) }
		assert_raise(ArgumentError) { iso.convert(F2_poly_mod.new(1, P4A)) }
	end

	def test_homomorphism_and_round_trip_all_elements
		(DEGREE_3_IRRS + DEGREE_4_IRRS).each do |source|
			irrs = source.degree == 3 ? DEGREE_3_IRRS : DEGREE_4_IRRS
			irrs.each do |target|
				next if source == target # Covered by identity test above.
				check_isomorphism(Field_isomorphism.new(source, target))
			end
		end
	end

	def test_every_root_gives_a_valid_isomorphism
		iso = Field_isomorphism.new(P3A, P3B)
		m = P3A.degree
		# Exactly m roots, hence exactly m distinct isomorphisms.
		assert_equal(m, iso.roots.length)
		image_bits = []
		iso.roots.each do |root|
			explicit = Field_isomorphism.new(P3A, P3B, root)
			check_isomorphism(explicit)
			image_bits.push(explicit.convert(F2_poly_mod.new(2, P3A)).residue.bits)
		end
		# Distinct roots give distinct generator images, hence
		# distinct isomorphisms.
		assert_equal(m, image_bits.uniq.length)
	end

	def test_roots_form_a_single_frobenius_orbit
		# The non-uniqueness is exactly the Galois group: squaring
		# (the Frobenius automorphism of the target field) permutes
		# the roots transitively.
		iso = Field_isomorphism.new(P3A, P3B)
		root_bits = iso.roots.collect{|r| r.bits}.sort
		orbit = []
		current = iso.roots[0]
		begin
			orbit.push(current.bits)
			squared = (F2_poly_mod.new(current, P3B) ** 2).residue
			current = squared
		end while current != iso.roots[0]
		assert_equal(root_bits, orbit.sort)
		assert_equal(P3A.degree, orbit.length)
	end

	# ------------------------------------------------------------
	# Verify, element by element over the whole (small) field, that
	# iso preserves addition and multiplication and that the inverse
	# map undoes it.
	def check_isomorphism(iso)
		source_elements = F2_poly_mod.elements_for_modulus(iso.source_modulus)
		assert_equal(F2_poly_mod.new(0, iso.target_modulus), iso.convert(0))
		assert_equal(F2_poly_mod.new(1, iso.target_modulus), iso.convert(1))
		source_elements.each do |a|
			source_elements.each do |b|
				assert_equal(iso.convert(a) + iso.convert(b), iso.convert(a + b))
				assert_equal(iso.convert(a) * iso.convert(b), iso.convert(a * b))
			end
		end
		inverse = iso.inverse
		source_elements.each do |a|
			assert_equal(a, inverse.convert(iso.convert(a)))
		end
	end

end
