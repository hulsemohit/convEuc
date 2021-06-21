theory equalanglesNC
	imports Axioms Definitions Theorems
begin

theorem equalanglesNC:
	assumes: `axioms`
		"ang_eq A B C a b c"
	shows: "\<not> col a b c"
proof -
	obtain U V u v where "ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C" sorry
	have "ray_on B A U" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by simp
	have "ray_on B C V" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by simp
	have "ray_on b a u" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by simp
	have "ray_on b c v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by simp
	have "seg_eq B U b u" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by simp
	have "seg_eq B V b v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by simp
	have "seg_eq U V u v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by simp
	have "\<not> col A B C" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by simp
	have "b \<noteq> a" using ray2[OF `axioms` `ray_on b a u`] .
	have "a \<noteq> b" using inequalitysymmetric[OF `axioms` `b \<noteq> a`] .
	have "seg_eq b u B U" using congruencesymmetric[OF `axioms` `seg_eq B U b u`] .
	have "seg_eq b v B V" using congruencesymmetric[OF `axioms` `seg_eq B V b v`] .
	have "col B A U" using rayimpliescollinear[OF `axioms` `ray_on B A U`] .
	have "col B C V" using rayimpliescollinear[OF `axioms` `ray_on B C V`] .
	have "col b a u" using rayimpliescollinear[OF `axioms` `ray_on b a u`] .
	have "col b c v" using rayimpliescollinear[OF `axioms` `ray_on b c v`] .
	have "col a b u" using collinearorder[OF `axioms` `col b a u`] by blast
