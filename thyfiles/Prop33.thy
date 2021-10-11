theory Prop33
	imports ABCequalsCBA Geometry NCorder Prop04 Prop27B Prop29B collinearorder congruenceflip equalanglestransitive
begin

theorem(in euclidean_geometry) Prop33:
	assumes 
		"parallel A B C D"
		"seg_eq A B C D"
		"bet A M D"
		"bet B M C"
	shows "parallel A C B D \<and> seg_eq A C B D"
proof -
	obtain a b c d m where "A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a m d \<and> bet c m b" using parallel_f[OF `parallel A B C D`]  by  blast
	have "\<not> (meets A B C D)" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a m d \<and> bet c m b` by blast
	have "A \<noteq> B" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a m d \<and> bet c m b` by blast
	have "C \<noteq> D" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a m d \<and> bet c m b` by blast
	have "col B M C" using collinear_b `bet B M C` by blast
	have "col B C M" using collinearorder[OF `col B M C`] by blast
	have "\<not> (col B C A)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B C A))"
hence "col B C A" by blast
		have "col A B C" using collinearorder[OF `col B C A`] by blast
		have "C = C" using equalityreflexiveE.
		have "col C D C" using collinear_b `C = C` by blast
		have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B C` `col C D C`] .
		show "False" using `meets A B C D` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a m d \<and> bet c m b` by blast
	qed
	hence "\<not> col B C A" by blast
	have "oppo_side A B C D" using oppositeside_b[OF `bet A M D` `col B C M` `\<not> col B C A`] .
	have "ang_eq A B C B C D" using Prop29B[OF `parallel A B C D` `oppo_side A B C D`] .
	have "\<not> (col B C D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B C D))"
hence "col B C D" by blast
		have "col C D B" using collinearorder[OF `col B C D`] by blast
		have "B = B" using equalityreflexiveE.
		have "col A B B" using collinear_b `B = B` by blast
		have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B B` `col C D B`] .
		have "\<not> (meets A B C D)" using `\<not> (meets A B C D)` .
		show "False" using `\<not> (meets A B C D)` `meets A B C D` by blast
	qed
	hence "\<not> col B C D" by blast
	have "ang_eq B C D D C B" using ABCequalsCBA[OF `\<not> col B C D`] .
	have "ang_eq A B C D C B" using equalanglestransitive[OF `ang_eq A B C B C D` `ang_eq B C D D C B`] .
	have "seg_eq B C B C" using congruencereflexiveE.
	have "\<not> col A B C" using NCorder[OF `\<not> col B C A`] by blast
	have "seg_eq B A C D" using congruenceflip[OF `seg_eq A B C D`] by blast
	have "seg_eq B C C B" using congruenceflip[OF `seg_eq B C B C`] by blast
	have "seg_eq A C D B \<and> ang_eq B A C C D B \<and> ang_eq B C A C B D" using Prop04[OF `seg_eq B A C D` `seg_eq B C C B` `ang_eq A B C D C B`] .
	have "seg_eq A C D B" using `seg_eq A C D B \<and> ang_eq B A C C D B \<and> ang_eq B C A C B D` by blast
	have "ang_eq B C A C B D" using `seg_eq A C D B \<and> ang_eq B A C C D B \<and> ang_eq B C A C B D` by blast
	have "\<not> col A C B" using NCorder[OF `\<not> col A B C`] by blast
	have "ang_eq A C B B C A" using ABCequalsCBA[OF `\<not> col A C B`] .
	have "ang_eq A C B C B D" using equalanglestransitive[OF `ang_eq A C B B C A` `ang_eq B C A C B D`] .
	have "seg_eq A C B D" using congruenceflip[OF `seg_eq A C D B`] by blast
	have "bet A M D" using `bet A M D` .
	have "col C B M" using collinearorder[OF `col B C M`] by blast
	have "\<not> col C B A" using NCorder[OF `\<not> col A B C`] by blast
	have "bet A M D \<and> col C B M \<and> \<not> col B C A" using `bet A M D` `col C B M` `\<not> col B C A` by blast
	have "oppo_side A C B D" using oppositeside_b[OF `bet A M D` `col C B M` `\<not> col C B A`] .
	have "parallel A C B D" using Prop27B[OF `ang_eq A C B C B D` `oppo_side A C B D`] .
	have "parallel A C B D \<and> seg_eq A C B D" using `parallel A C B D` `seg_eq A C B D` by blast
	thus ?thesis by blast
qed

end