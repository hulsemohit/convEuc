theory Prop04
	imports Geometry betweennesspreserved betweennotequal collinearorder congruenceflip congruencesymmetric congruencetransitive differenceofparts equalanglesNC inequalitysymmetric interior5 layoffunique lessthancongruence partnotequalwhole ray1 ray2 ray3 ray4 ray5
begin

theorem Prop04:
	assumes "axioms"
		"seg_eq A B a b"
		"seg_eq A C a c"
		"ang_eq B A C b a c"
	shows "seg_eq B C b c \<and> ang_eq A B C a b c \<and> ang_eq A C B a c b"
proof -
	have "\<not> col b a c" using equalanglesNC[OF `axioms` `ang_eq B A C b a c`] .
	obtain U V u v where "ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C" using equalangles_f[OF `axioms` `ang_eq B A C b a c`]  by  blast
	have "ray_on A B U" using `ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C` by blast
	have "ray_on a b u" using `ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C` by blast
	have "ray_on a c v" using `ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C` by blast
	have "seg_eq A V a v" using `ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C` by blast
	have "seg_eq U V u v" using `ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C` by blast
	have "\<not> col B A C" using `ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C` by blast
	have "a \<noteq> b" using ray2[OF `axioms` `ray_on a b u`] .
	have "b \<noteq> a" using inequalitysymmetric[OF `axioms` `a \<noteq> b`] .
	have "\<not> (col A B C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A B C))"
hence "col A B C" by blast
		have "col B A C" using collinearorder[OF `axioms` `col A B C`] by blast
		show "False" using `col B A C` `ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C` by blast
	qed
	hence "\<not> col A B C" by blast
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> B)"
		hence "A = B" by blast
		have "col A B C" using collinear_b `axioms` `A = B` by blast
		have "col B A C" using collinearorder[OF `axioms` `col A B C`] by blast
		show "False" using `col B A C` `ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> C)"
		hence "A = C" by blast
		have "col A B C" using collinear_b `axioms` `A = C` by blast
		have "col B A C" using collinearorder[OF `axioms` `col A B C`] by blast
		show "False" using `col B A C` `ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C` by blast
	qed
	hence "A \<noteq> C" by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> C`] .
	have "\<not> (a = c)"
	proof (rule ccontr)
		assume "\<not> (a \<noteq> c)"
		hence "a = c" by blast
		have "col b a c" using collinear_b `axioms` `a = c` by blast
		show "False" using `col b a c` `\<not> col b a c` by blast
	qed
	hence "a \<noteq> c" by blast
	have "c \<noteq> a" using inequalitysymmetric[OF `axioms` `a \<noteq> c`] .
	have "\<not> (b = c)"
	proof (rule ccontr)
		assume "\<not> (b \<noteq> c)"
		hence "b = c" by blast
		have "col b a c" using collinear_b `axioms` `b = c` by blast
		show "False" using `col b a c` `\<not> col b a c` by blast
	qed
	hence "b \<noteq> c" by blast
	have "c \<noteq> b" using inequalitysymmetric[OF `axioms` `b \<noteq> c`] .
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> C)"
		hence "B = C" by blast
		have "col A B C" using collinear_b `axioms` `B = C` by blast
		have "col B A C" using collinearorder[OF `axioms` `col A B C`] by blast
		show "False" using `col B A C` `ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	have "bet A U B \<or> B = U \<or> bet A B U" using ray1[OF `axioms` `ray_on A B U`] .
	consider "bet A U B"|"B = U"|"bet A B U" using `bet A U B \<or> B = U \<or> bet A B U`  by blast
	hence "seg_eq B V b v"
	proof (cases)
		assume "bet A U B"
		have "seg_eq A U a u" using `ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C` by blast
		have "seg_eq A B a b" using `seg_eq A B a b` .
		have "seg_eq A U A U" using congruencereflexiveE[OF `axioms`] .
		have "seg_lt A U A B" using lessthan_b[OF `axioms` `bet A U B` `seg_eq A U A U`] .
		have "seg_lt A U a b" using lessthancongruence[OF `axioms` `seg_lt A U A B` `seg_eq A B a b`] .
		obtain w where "bet a w b \<and> seg_eq a w A U" using lessthan_f[OF `axioms` `seg_lt A U a b`]  by  blast
		have "bet a w b" using `bet a w b \<and> seg_eq a w A U` by blast
		have "seg_eq a w A U" using `bet a w b \<and> seg_eq a w A U` by blast
		have "seg_eq a w a u" using congruencetransitive[OF `axioms` `seg_eq a w A U` `seg_eq A U a u`] .
		have "a \<noteq> b" using betweennotequal[OF `axioms` `bet a w b`] by blast
		have "ray_on a b w" using ray4 `axioms` `bet a w b \<and> seg_eq a w A U` `a \<noteq> b` by blast
		have "seg_eq a w a u" using congruencetransitive[OF `axioms` `seg_eq a w A U` `seg_eq A U a u`] .
		have "w = u" using layoffunique[OF `axioms` `ray_on a b w` `ray_on a b u` `seg_eq a w a u`] .
		have "bet a u b" using `bet a w b` `w = u` by blast
		have "seg_eq U B u b" using differenceofparts[OF `axioms` `seg_eq A U a u` `seg_eq A B a b` `bet A U B` `bet a u b`] .
		have "seg_eq U V u v" using `seg_eq U V u v` .
		have "seg_eq A V a v" using `seg_eq A V a v` .
		have "seg_eq A U a u" using `seg_eq A U a u` .
		have "seg_eq V B v b" using n5_lineE[OF `axioms` `seg_eq U B u b` `seg_eq A V a v` `seg_eq U V u v` `bet A U B` `bet a u b` `seg_eq A U a u`] .
		have "seg_eq B V b v" using congruenceflip[OF `axioms` `seg_eq V B v b`] by blast
		thus ?thesis by blast
	next
		assume "B = U"
		have "seg_eq U V u v" using `seg_eq U V u v` .
		have "seg_eq B V u v" using `seg_eq U V u v` `B = U` by blast
		have "seg_eq a b A B" using congruencesymmetric[OF `axioms` `seg_eq A B a b`] .
		have "seg_eq A B A B" using congruencereflexiveE[OF `axioms`] .
		have "seg_eq A B A U" using `seg_eq A B A B` `B = U` by blast
		have "seg_eq A U a u" using `ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C` by blast
		have "seg_eq a b A U" using congruencetransitive[OF `axioms` `seg_eq a b A B` `seg_eq A B A U`] .
		have "seg_eq a b a u" using congruencetransitive[OF `axioms` `seg_eq a b A U` `seg_eq A U a u`] .
		have "bet a u b \<or> b = u \<or> bet a b u" using ray1[OF `axioms` `ray_on a b u`] .
		consider "bet a u b"|"b = u"|"bet a b u" using `bet a u b \<or> b = u \<or> bet a b u`  by blast
		hence "b = u"
		proof (cases)
			assume "bet a u b"
			have "\<not> (b \<noteq> u)"
			proof (rule ccontr)
				assume "\<not> (\<not> (b \<noteq> u))"
hence "b \<noteq> u" by blast
				have "\<not> (seg_eq a u a b)" using partnotequalwhole[OF `axioms` `bet a u b`] .
				have "seg_eq a u a b" using congruencesymmetric[OF `axioms` `seg_eq a b a u`] .
				show "False" using `seg_eq a u a b` `\<not> (seg_eq a u a b)` by blast
			qed
			hence "b = u" by blast
			thus ?thesis by blast
		next
			assume "b = u"
			thus ?thesis by blast
		next
			assume "bet a b u"
			have "\<not> (b \<noteq> u)"
			proof (rule ccontr)
				assume "\<not> (\<not> (b \<noteq> u))"
hence "b \<noteq> u" by blast
				have "\<not> (seg_eq a b a u)" using partnotequalwhole[OF `axioms` `bet a b u`] .
				have "seg_eq a b A B" using congruencesymmetric[OF `axioms` `seg_eq A B a b`] .
				have "seg_eq A B A B" using congruencereflexiveE[OF `axioms`] .
				have "seg_eq A B A U" using `seg_eq A B A B` `B = U` by blast
				have "seg_eq A U a u" using `seg_eq A U a u` .
				have "seg_eq A B a u" using congruencetransitive[OF `axioms` `seg_eq A B A U` `seg_eq A U a u`] .
				have "seg_eq a b a u" using congruencetransitive[OF `axioms` `seg_eq a b A B` `seg_eq A B a u`] .
				show "False" using `seg_eq a b a u` `\<not> (seg_eq a b a u)` by blast
			qed
			hence "b = u" by blast
			thus ?thesis by blast
		qed
		have "seg_eq U V u v" using `seg_eq U V u v` .
		have "seg_eq B V b v" using `seg_eq B V u v` `b = u` by blast
		thus ?thesis by blast
	next
		assume "bet A B U"
		have "seg_eq A U a u" using `ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C` by blast
		have "seg_eq A B A B" using congruencereflexiveE[OF `axioms`] .
		have "seg_lt A B A U" using lessthan_b[OF `axioms` `bet A B U` `seg_eq A B A B`] .
		have "seg_lt A B a u" using lessthancongruence[OF `axioms` `seg_lt A B A U` `seg_eq A U a u`] .
		obtain f where "bet a f u \<and> seg_eq a f A B" using lessthan_f[OF `axioms` `seg_lt A B a u`]  by  blast
		have "bet a f u" using `bet a f u \<and> seg_eq a f A B` by blast
		have "a \<noteq> u" using betweennotequal[OF `axioms` `bet a f u`] by blast
		have "ray_on a u f" using ray4 `axioms` `bet a f u \<and> seg_eq a f A B` `a \<noteq> u` by blast
		have "ray_on a b u" using `ray_on a b u` .
		have "ray_on a u b" using ray5[OF `axioms` `ray_on a b u`] .
		have "ray_on a b f" using ray3[OF `axioms` `ray_on a u b` `ray_on a u f`] .
		have "seg_eq a f A B" using `bet a f u \<and> seg_eq a f A B` by blast
		have "seg_eq A B a b" using `seg_eq A B a b` .
		have "seg_eq a f a b" using congruencetransitive[OF `axioms` `seg_eq a f A B` `seg_eq A B a b`] .
		have "f = b" using layoffunique[OF `axioms` `ray_on a u f` `ray_on a u b` `seg_eq a f a b`] .
		have "bet a b u" using `bet a f u` `f = b` by blast
		have "seg_eq B U b u" using differenceofparts[OF `axioms` `seg_eq A B a b` `seg_eq A U a u` `bet A B U` `bet a b u`] .
		have "bet a b u" using betweennesspreserved[OF `axioms` `seg_eq A B a b` `seg_eq A U a u` `seg_eq B U b u` `bet A B U`] .
		have "seg_eq A B a b" using `seg_eq A B a b` .
		have "seg_eq B U b u" using differenceofparts[OF `axioms` `seg_eq A B a b` `seg_eq A U a u` `bet A B U` `bet a b u`] .
		have "seg_eq A V a v" using `seg_eq A V a v` .
		have "seg_eq U V u v" using `seg_eq U V u v` .
		have "seg_eq B V b v" using interior5[OF `axioms` `bet A B U` `bet a b u` `seg_eq A B a b` `seg_eq B U b u` `seg_eq A V a v` `seg_eq U V u v`] .
		thus ?thesis by blast
	qed
	have "ray_on A C V" using `ray_on A B U \<and> ray_on A C V \<and> ray_on a b u \<and> ray_on a c v \<and> seg_eq A U a u \<and> seg_eq A V a v \<and> seg_eq U V u v \<and> \<not> col B A C` by blast
	have "bet A V C \<or> C = V \<or> bet A C V" using ray1[OF `axioms` `ray_on A C V`] .
	consider "bet A V C"|"C = V"|"bet A C V" using `bet A V C \<or> C = V \<or> bet A C V`  by blast
	hence "seg_eq B C b c"
	proof (cases)
		assume "bet A V C"
		have "seg_eq A V a v" using `seg_eq A V a v` .
		have "seg_eq A V A V" using congruencereflexiveE[OF `axioms`] .
		have "seg_lt A V A C" using lessthan_b[OF `axioms` `bet A V C` `seg_eq A V A V`] .
		have "seg_lt A V a c" using lessthancongruence[OF `axioms` `seg_lt A V A C` `seg_eq A C a c`] .
		obtain g where "bet a g c \<and> seg_eq a g A V" using lessthan_f[OF `axioms` `seg_lt A V a c`]  by  blast
		have "bet a g c" using `bet a g c \<and> seg_eq a g A V` by blast
		have "a \<noteq> g" using betweennotequal[OF `axioms` `bet a g c`] by blast
		have "ray_on a g c" using ray4 `axioms` `bet a g c \<and> seg_eq a g A V` `a \<noteq> g` by blast
		have "ray_on a c g" using ray5[OF `axioms` `ray_on a g c`] .
		have "ray_on a c v" using `ray_on a c v` .
		have "seg_eq a g A V" using `bet a g c \<and> seg_eq a g A V` by blast
		have "seg_eq a g a v" using congruencetransitive[OF `axioms` `seg_eq a g A V` `seg_eq A V a v`] .
		have "g = v" using layoffunique[OF `axioms` `ray_on a c g` `ray_on a c v` `seg_eq a g a v`] .
		have "bet a v c" using `bet a g c` `g = v` by blast
		have "seg_eq V C v c" using differenceofparts[OF `axioms` `seg_eq A V a v` `seg_eq A C a c` `bet A V C` `bet a v c`] .
		have "seg_eq A B a b" using `seg_eq A B a b` .
		have "seg_eq A V a v" using `seg_eq A V a v` .
		have "seg_eq V C v c" using `seg_eq V C v c` .
		have "seg_eq V B v b" using congruenceflip[OF `axioms` `seg_eq B V b v`] by blast
		have "seg_eq B C b c" using n5_lineE[OF `axioms` `seg_eq V C v c` `seg_eq A B a b` `seg_eq V B v b` `bet A V C` `bet a v c` `seg_eq A V a v`] .
		thus ?thesis by blast
	next
		assume "C = V"
		have "seg_eq A V a v" using `seg_eq A V a v` .
		have "seg_eq A C a v" using `seg_eq A V a v` `C = V` by blast
		have "seg_eq A C a c" using `seg_eq A C a c` .
		have "seg_eq a c A C" using congruencesymmetric[OF `axioms` `seg_eq A C a c`] .
		have "seg_eq a c a v" using congruencetransitive[OF `axioms` `seg_eq a c A C` `seg_eq A C a v`] .
		have "ray_on a c v" using `ray_on a c v` .
		have "a \<noteq> c" using ray2[OF `axioms` `ray_on a c v`] .
		have "c = c" using equalityreflexiveE[OF `axioms`] .
		have "ray_on a c c" using ray4 `axioms` `c = c` `a \<noteq> c` by blast
		have "c = v" using layoffunique[OF `axioms` `ray_on a c c` `ray_on a c v` `seg_eq a c a v`] .
		have "seg_eq B C b v" using `seg_eq B V b v` `C = V` by blast
		have "seg_eq B C b c" using `seg_eq B C b v` `c = v` by blast
		thus ?thesis by blast
	next
		assume "bet A C V"
		have "seg_eq A V a v" using `seg_eq A V a v` .
		have "seg_eq A C A C" using congruencereflexiveE[OF `axioms`] .
		have "seg_lt A C A V" using lessthan_b[OF `axioms` `bet A C V` `seg_eq A C A C`] .
		have "seg_lt A C a v" using lessthancongruence[OF `axioms` `seg_lt A C A V` `seg_eq A V a v`] .
		obtain g where "bet a g v \<and> seg_eq a g A C" using lessthan_f[OF `axioms` `seg_lt A C a v`]  by  blast
		have "bet a g v" using `bet a g v \<and> seg_eq a g A C` by blast
		have "seg_eq a g A C" using `bet a g v \<and> seg_eq a g A C` by blast
		have "a \<noteq> g" using betweennotequal[OF `axioms` `bet a g v`] by blast
		have "ray_on a g v" using ray4 `axioms` `bet a g v \<and> seg_eq a g A C` `a \<noteq> g` by blast
		have "ray_on a v g" using ray5[OF `axioms` `ray_on a g v`] .
		have "seg_eq a g a c" using congruencetransitive[OF `axioms` `seg_eq a g A C` `seg_eq A C a c`] .
		have "seg_eq a c a g" using congruencesymmetric[OF `axioms` `seg_eq a g a c`] .
		have "ray_on a v c" using ray5[OF `axioms` `ray_on a c v`] .
		have "c = g" using layoffunique[OF `axioms` `ray_on a v c` `ray_on a v g` `seg_eq a c a g`] .
		have "bet a c v" using `bet a g v` `c = g` by blast
		have "seg_eq C V c v" using differenceofparts[OF `axioms` `seg_eq A C a c` `seg_eq A V a v` `bet A C V` `bet a c v`] .
		have "seg_eq A B a b" using `seg_eq A B a b` .
		have "seg_eq V B v b" using congruenceflip[OF `axioms` `seg_eq B V b v`] by blast
		have "seg_eq C B c b" using interior5[OF `axioms` `bet A C V` `bet a c v` `seg_eq A C a c` `seg_eq C V c v` `seg_eq A B a b` `seg_eq V B v b`] .
		have "seg_eq B C b c" using congruenceflip[OF `axioms` `seg_eq C B c b`] by blast
		thus ?thesis by blast
	qed
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "a = a" using equalityreflexiveE[OF `axioms`] .
	have "c = c" using equalityreflexiveE[OF `axioms`] .
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "b = b" using equalityreflexiveE[OF `axioms`] .
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "ray_on B A A" using ray4 `axioms` `A = A` `B \<noteq> A` by blast
	have "ray_on B C C" using ray4 `axioms` `C = C` `B \<noteq> C` by blast
	have "ray_on b a a" using ray4 `axioms` `a = a` `b \<noteq> a` by blast
	have "ray_on b c c" using ray4 `axioms` `c = c` `b \<noteq> c` by blast
	have "seg_eq B A b a" using congruenceflip[OF `axioms` `seg_eq A B a b`] by blast
	have "seg_eq B C b c" using `seg_eq B C b c` .
	have "seg_eq A C a c" using `seg_eq A C a c` .
	have "\<not> col A B C" using `\<not> col A B C` .
	have "ang_eq A B C a b c" using equalangles_b[OF `axioms` `ray_on B A A` `ray_on B C C` `ray_on b a a` `ray_on b c c` `seg_eq B A b a` `seg_eq B C b c` `seg_eq A C a c` `\<not> col A B C`] .
	have "ray_on C A A" using ray4 `axioms` `A = A` `C \<noteq> A` by blast
	have "ray_on C B B" using ray4 `axioms` `B = B` `C \<noteq> B` by blast
	have "ray_on c a a" using ray4 `axioms` `a = a` `c \<noteq> a` by blast
	have "ray_on c b b" using ray4 `axioms` `b = b` `c \<noteq> b` by blast
	have "seg_eq C A c a" using congruenceflip[OF `axioms` `seg_eq A C a c`] by blast
	have "seg_eq C B c b" using congruenceflip[OF `axioms` `seg_eq B C b c`] by blast
	have "seg_eq A B a b" using `seg_eq A B a b` .
	have "\<not> (col A C B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A C B))"
hence "col A C B" by blast
		have "col A B C" using collinearorder[OF `axioms` `col A C B`] by blast
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "\<not> col A C B" by blast
	have "ang_eq A C B a c b" using equalangles_b[OF `axioms` `ray_on C A A` `ray_on C B B` `ray_on c a a` `ray_on c b b` `seg_eq C A c a` `seg_eq C B c b` `seg_eq A B a b` `\<not> col A C B`] .
	have "seg_eq B C b c \<and> ang_eq A B C a b c \<and> ang_eq A C B a c b" using `seg_eq B C b c` `ang_eq A B C a b c` `ang_eq A C B a c b` by blast
	thus ?thesis by blast
qed

end