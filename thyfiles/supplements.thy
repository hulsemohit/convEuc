theory supplements
	imports n3_6a n3_7a n3_7b Geometry betweennotequal collinear4 collinearorder congruenceflip congruencesymmetric congruencetransitive inequalitysymmetric ray1 ray3 rayimpliescollinear raystrict
begin

theorem(in euclidean_geometry) supplements:
	assumes 
		"ang_eq A B C a b c"
		"supplement A B C D F"
		"supplement a b c d f"
	shows "ang_eq D B F d b f"
proof -
	have "bet A B F" using supplement_f[OF `supplement A B C D F`] by blast
	have "ray_on B C D" using supplement_f[OF `supplement A B C D F`] by blast
	have "bet a b f" using supplement_f[OF `supplement a b c d f`] by blast
	have "ray_on b c d" using supplement_f[OF `supplement a b c d f`] by blast
	have "ang_eq A B C a b c" using `ang_eq A B C a b c` .
	obtain U V u v where "ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C" using equalangles_f[OF `ang_eq A B C a b c`]  by  blast
	have "ray_on B A U" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "ray_on B C V" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "ray_on b a u" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "ray_on b c v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "seg_eq B U b u" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "B \<noteq> U" using raystrict[OF `ray_on B A U`] .
	have "U \<noteq> B" using inequalitysymmetric[OF `B \<noteq> U`] .
	have "b \<noteq> u" using raystrict[OF `ray_on b a u`] .
	have "u \<noteq> b" using inequalitysymmetric[OF `b \<noteq> u`] .
	obtain W where "bet U B W \<and> seg_eq B W U B" using extensionE[OF `U \<noteq> B` `U \<noteq> B`]  by  blast
	have "bet U B W" using `bet U B W \<and> seg_eq B W U B` by blast
	have "bet a b f" using `bet a b f` .
	obtain w where "bet u b w \<and> seg_eq b w U B" using extensionE[OF `u \<noteq> b` `U \<noteq> B`]  by  blast
	have "bet u b w" using `bet u b w \<and> seg_eq b w U B` by blast
	have "seg_eq b w U B" using `bet u b w \<and> seg_eq b w U B` by blast
	have "seg_eq B W U B" using `bet U B W \<and> seg_eq B W U B` by blast
	have "seg_eq U B b w" using congruencesymmetric[OF `seg_eq b w U B`] .
	have "seg_eq B W b w" using congruencetransitive[OF `seg_eq B W U B` `seg_eq U B b w`] .
	have "seg_eq U B u b" using congruenceflip[OF `seg_eq B U b u`] by blast
	have "seg_eq U V u v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "seg_eq B V b v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "bet U B W" using `bet U B W` .
	have "bet u b w" using `bet u b w` .
	have "seg_eq V W v w" using n5_lineE[OF `seg_eq B W b w` `seg_eq U V u v` `seg_eq B V b v` `bet U B W` `bet u b w` `seg_eq U B u b`] .
	have "bet U B W" using `bet U B W` .
	have "bet A B F" using `bet A B F` .
	have "ray_on B A U" using `ray_on B A U` .
	have "bet B U A \<or> A = U \<or> bet B A U" using ray1[OF `ray_on B A U`] .
	consider "bet B U A"|"A = U"|"bet B A U" using `bet B U A \<or> A = U \<or> bet B A U`  by blast
	hence "bet A B W"
	proof (cases)
		assume "bet B U A"
		have "bet A U B" using betweennesssymmetryE[OF `bet B U A`] .
		have "bet U B W" using `bet U B W` .
		have "bet A B W" using n3_7a[OF `bet A U B` `bet U B W`] .
		thus ?thesis by blast
	next
		assume "A = U"
		have "bet A B W" using `bet U B W` `A = U` by blast
		thus ?thesis by blast
	next
		assume "bet B A U"
		have "bet U A B" using betweennesssymmetryE[OF `bet B A U`] .
		have "bet U B W" using `bet U B W` .
		have "bet A B W" using n3_6a[OF `bet U A B` `bet U B W`] .
		thus ?thesis by blast
	qed
	have "ray_on B F W" using ray_b[OF `bet A B W` `bet A B F`] .
	have "bet B W F \<or> F = W \<or> bet B F W" using ray1[OF `ray_on B F W`] .
	consider "bet B W F"|"F = W"|"bet B F W" using `bet B W F \<or> F = W \<or> bet B F W`  by blast
	hence "bet U B F"
	proof (cases)
		assume "bet B W F"
		have "bet U B F" using n3_7b[OF `bet U B W` `bet B W F`] .
		thus ?thesis by blast
	next
		assume "F = W"
		have "bet U B F" using `bet U B W` `F = W` by blast
		thus ?thesis by blast
	next
		assume "bet B F W"
		have "bet U B F" using innertransitivityE[OF `bet U B W` `bet B F W`] .
		thus ?thesis by blast
	qed
	have "bet b u a \<or> a = u \<or> bet b a u" using ray1[OF `ray_on b a u`] .
	consider "bet b u a"|"a = u"|"bet b a u" using `bet b u a \<or> a = u \<or> bet b a u`  by blast
	hence "bet a b w"
	proof (cases)
		assume "bet b u a"
		have "bet a u b" using betweennesssymmetryE[OF `bet b u a`] .
		have "bet u b w" using `bet u b w` .
		have "bet a b w" using n3_7a[OF `bet a u b` `bet u b w`] .
		thus ?thesis by blast
	next
		assume "a = u"
		have "bet a b w" using `bet u b w` `a = u` by blast
		thus ?thesis by blast
	next
		assume "bet b a u"
		have "bet u a b" using betweennesssymmetryE[OF `bet b a u`] .
		have "bet u b w" using `bet u b w` .
		have "bet a b w" using n3_6a[OF `bet u a b` `bet u b w`] .
		thus ?thesis by blast
	qed
	have "ray_on b f w" using ray_b[OF `bet a b w` `bet a b f`] .
	have "\<not> (col D B F)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col D B F))"
hence "col D B F" by blast
		have "col B C D" using rayimpliescollinear[OF `ray_on B C D`] .
		have "col D B C" using collinearorder[OF `col B C D`] by blast
		have "B \<noteq> D" using raystrict[OF `ray_on B C D`] .
		have "D \<noteq> B" using inequalitysymmetric[OF `B \<noteq> D`] .
		have "col B F C" using collinear4[OF `col D B F` `col D B C` `D \<noteq> B`] .
		have "col A B F" using collinear_b `bet A B F` by blast
		have "col F B A" using collinearorder[OF `col A B F`] by blast
		have "col F B C" using collinearorder[OF `col B F C`] by blast
		have "B \<noteq> F" using betweennotequal[OF `bet A B F`] by blast
		have "F \<noteq> B" using inequalitysymmetric[OF `B \<noteq> F`] .
		have "col B A C" using collinear4[OF `col F B A` `col F B C` `F \<noteq> B`] .
		have "col A B C" using collinearorder[OF `col B A C`] by blast
		have "\<not> col A B C" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "\<not> col D B F" by blast
	have "ray_on B D V" using ray3[OF `ray_on B C D` `ray_on B C V`] .
	have "ray_on B F W" using `ray_on B F W` .
	have "ray_on b d v" using ray3[OF `ray_on b c d` `ray_on b c v`] .
	have "ray_on b f w" using `ray_on b f w` .
	have "seg_eq B V b v" using `seg_eq B V b v` .
	have "seg_eq B W b w" using `seg_eq B W b w` .
	have "seg_eq V W v w" using `seg_eq V W v w` .
	have "ang_eq D B F d b f" using equalangles_b[OF `ray_on B D V` `ray_on B F W` `ray_on b d v` `ray_on b f w` `seg_eq B V b v` `seg_eq B W b w` `seg_eq V W v w` `\<not> col D B F`] .
	thus ?thesis by blast
qed

end