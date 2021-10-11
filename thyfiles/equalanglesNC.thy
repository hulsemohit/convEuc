theory equalanglesNC
	imports Geometry collinear4 collinearitypreserved collinearorder congruencesymmetric inequalitysymmetric ray2 rayimpliescollinear raystrict
begin

theorem(in euclidean_geometry) equalanglesNC:
	assumes 
		"ang_eq A B C a b c"
	shows "\<not> col a b c"
proof -
	obtain U V u v where "ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C" using equalangles_f[OF `ang_eq A B C a b c`]  by  blast
	have "ray_on B A U" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "ray_on B C V" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "ray_on b a u" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "ray_on b c v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "seg_eq B U b u" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "seg_eq B V b v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "seg_eq U V u v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "\<not> col A B C" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "b \<noteq> a" using ray2[OF `ray_on b a u`] .
	have "a \<noteq> b" using inequalitysymmetric[OF `b \<noteq> a`] .
	have "seg_eq b u B U" using congruencesymmetric[OF `seg_eq B U b u`] .
	have "seg_eq b v B V" using congruencesymmetric[OF `seg_eq B V b v`] .
	have "col B A U" using rayimpliescollinear[OF `ray_on B A U`] .
	have "col B C V" using rayimpliescollinear[OF `ray_on B C V`] .
	have "col b a u" using rayimpliescollinear[OF `ray_on b a u`] .
	have "col b c v" using rayimpliescollinear[OF `ray_on b c v`] .
	have "col a b u" using collinearorder[OF `col b a u`] by blast
	have "\<not> (col a b c)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col a b c))"
hence "col a b c" by blast
		have "col b u c" using collinear4[OF `col a b u` `col a b c` `a \<noteq> b`] .
		have "col c b u" using collinearorder[OF `col b u c`] by blast
		have "col c b v" using collinearorder[OF `col b c v`] by blast
		have "b \<noteq> c" using ray2[OF `ray_on b c v`] .
		have "c \<noteq> b" using inequalitysymmetric[OF `b \<noteq> c`] .
		have "col b u v" using collinear4[OF `col c b u` `col c b v` `c \<noteq> b`] .
		have "seg_eq b u B U" using `seg_eq b u B U` .
		have "seg_eq b v B V" using `seg_eq b v B V` .
		have "seg_eq u v U V" using congruencesymmetric[OF `seg_eq U V u v`] .
		have "col B U V" using collinearitypreserved[OF `col b u v` `seg_eq b u B U` `seg_eq b v B V` `seg_eq u v U V`] .
		have "col B A U" using `col B A U` .
		have "col B U A" using collinearorder[OF `col B A U`] by blast
		have "B \<noteq> U" using raystrict[OF `ray_on B A U`] .
		have "col U V A" using collinear4[OF `col B U V` `col B U A` `B \<noteq> U`] .
		have "col U V B" using collinearorder[OF `col B U V`] by blast
		consider "U = V"|"U \<noteq> V" by blast
		hence "col V A B"
		proof (cases)
			assume "U = V"
			have "col B A U" using `col B A U` .
			have "col B A V" using `col B A U` `U = V` by blast
			have "col V A B" using collinearorder[OF `col B A V`] by blast
			thus ?thesis by blast
		next
			assume "U \<noteq> V"
			have "col V A B" using collinear4[OF `col U V A` `col U V B` `U \<noteq> V`] .
			thus ?thesis by blast
		qed
		have "col V B A" using collinearorder[OF `col V A B`] by blast
		have "col V B C" using collinearorder[OF `col B C V`] by blast
		have "B \<noteq> V" using raystrict[OF `ray_on B C V`] .
		have "V \<noteq> B" using inequalitysymmetric[OF `B \<noteq> V`] .
		have "col B A C" using collinear4[OF `col V B A` `col V B C` `V \<noteq> B`] .
		have "col A B C" using collinearorder[OF `col B A C`] by blast
		show "False" using `col A B C` `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	qed
	hence "\<not> col a b c" by blast
	thus ?thesis by blast
qed

end