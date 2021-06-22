theory Prop29B
	imports Axioms Definitions Theorems
begin

theorem Prop29B:
	assumes: `axioms`
		"parallel A G H D"
		"oppo_side A G H D"
	shows: "ang_eq A G H G H D"
proof -
	obtain a d g h m where "A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g" using parallel_f[OF `axioms` `parallel A G H D`] by blast
	have "A \<noteq> G" using `A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g` by blast
	have "H \<noteq> D" using `A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g` by blast
	have "D \<noteq> H" using inequalitysymmetric[OF `axioms` `H \<noteq> D`] .
	have "col A G a" using `A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g` by blast
	have "col A G g" using `A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g` by blast
	have "a \<noteq> g" using `A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g` by blast
	have "h \<noteq> d" using `A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g` by blast
	have "bet a m d" using `A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g` by blast
	have "bet h m g" using `A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g` by blast
	have "\<not> (H = G)"
	proof (rule ccontr)
		assume "H = G"
		have "H = H" using equalityreflexiveE[OF `axioms`] .
		have "col H D H" using collinear_b `axioms` `H = H` by blast
		have "G = G" using equalityreflexiveE[OF `axioms`] .
		have "col A G G" using collinear_b `axioms` `G = G` by blast
		have "col A G H" using `col A G G` `H = G` by blast
		have "meets A G H D" using meet_b[OF `axioms` `A \<noteq> G` `H \<noteq> D` `col A G H` `col H D H`] .
		have "\<not> (meets A G H D)" using `A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g` by blast
		show "False" using `\<not> (meets A G H D)` `meets A G H D` by blast
	qed
	hence "H \<noteq> G" by blast
	obtain B where "bet A G B \<and> seg_eq G B A G" using extensionE[OF `axioms` `A \<noteq> G` `A \<noteq> G`] by blast
	obtain C where "bet D H C \<and> seg_eq H C D H" using extensionE[OF `axioms` `D \<noteq> H` `D \<noteq> H`] by blast
	obtain E where "bet H G E \<and> seg_eq G E H G" using extensionE[OF `axioms` `H \<noteq> G` `H \<noteq> G`] by blast
	have "bet A G B" using `bet A G B \<and> seg_eq G B A G` by blast
	have "bet D H C" using `bet D H C \<and> seg_eq H C D H` by blast
	have "bet H G E" using `bet H G E \<and> seg_eq G E H G` by blast
	have "A \<noteq> B" using betweennotequal[OF `axioms` `bet A G B`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "D \<noteq> C" using betweennotequal[OF `axioms` `bet D H C`] by blast
	have "C \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> C`] .
	have "col A G B" using collinear_b `axioms` `bet A G B \<and> seg_eq G B A G` by blast
	have "col G A B" using collinearorder[OF `axioms` `col A G B`] by blast
	have "col G A a" using collinearorder[OF `axioms` `col A G a`] by blast
	have "G \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> G`] .
	have "col A B a" using collinear4[OF `axioms` `col G A B` `col G A a` `G \<noteq> A`] .
	have "col G A g" using collinearorder[OF `axioms` `col A G g`] by blast
	have "col A B g" using collinear4[OF `axioms` `col G A B` `col G A g` `G \<noteq> A`] .
	have "col D H C" using collinear_b `axioms` `bet D H C \<and> seg_eq H C D H` by blast
	have "col H D C" using collinearorder[OF `axioms` `col D H C`] by blast
	have "col H D h" using `A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g` by blast
	have "col D C h" using collinear4[OF `axioms` `col H D C` `col H D h` `H \<noteq> D`] .
	have "col C D h" using collinearorder[OF `axioms` `col D C h`] by blast
	have "col H D d" using `A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g` by blast
	have "col D d C" using collinear4[OF `axioms` `col H D d` `col H D C` `H \<noteq> D`] .
	have "col C D d" using collinearorder[OF `axioms` `col D d C`] by blast
	have "col A B a" using `col A B a` .
	have "col A B g" using `col A B g` .
	have "col C D h" using `col C D h` .
	have "col C D d" using `col C D d` .
	have "\<not> (meets A B C D)"
	proof (rule ccontr)
		assume "meets A B C D"
		obtain M where "A \<noteq> B \<and> C \<noteq> D \<and> col A B M \<and> col C D M" using meet_f[OF `axioms` `meets A B C D`] by blast
		have "col A B M" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B M \<and> col C D M` by blast
		have "col C D M" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B M \<and> col C D M` by blast
		have "col B A G" using collinearorder[OF `axioms` `col A G B`] by blast
		have "col B A M" using collinearorder[OF `axioms` `col A B M`] by blast
		have "col A G M" using collinear4[OF `axioms` `col B A G` `col B A M` `B \<noteq> A`] .
		have "col C D H" using collinearorder[OF `axioms` `col D H C`] by blast
		have "col D H M" using collinear4[OF `axioms` `col C D H` `col C D M` `C \<noteq> D`] .
		have "col H D M" using collinearorder[OF `axioms` `col D H M`] by blast
		have "A \<noteq> G \<and> H \<noteq> D \<and> col A G M \<and> col H D M" using `A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g` `A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g` `col A G M` `col H D M` by blast
		have "meets A G H D" using meet_b[OF `axioms` `A \<noteq> G` `H \<noteq> D` `col A G M` `col H D M`] .
		have "\<not> (meets A G H D)" using `A \<noteq> G \<and> H \<noteq> D \<and> col A G a \<and> col A G g \<and> a \<noteq> g \<and> col H D h \<and> col H D d \<and> h \<noteq> d \<and> \<not> (meets A G H D) \<and> bet a m d \<and> bet h m g` by blast
		show "False" using `\<not> (meets A G H D)` `meets A G H D` by blast
	qed
	hence "\<not> (meets A B C D)" by blast
	have "parallel A B C D" using parallel_b[OF `axioms` `A \<noteq> B` `C \<noteq> D` `col A B a` `col A B g` `a \<noteq> g` `col C D h` `col C D d` `h \<noteq> d` `\<not> (meets A B C D)` `bet a m d` `bet h m g`] .
	have "bet A G B" using `bet A G B` .
	have "bet C H D" using betweennesssymmetryE[OF `axioms` `bet D H C`] .
	have "bet E G H" using betweennesssymmetryE[OF `axioms` `bet H G E`] .
	have "ang_eq A G H G H D \<and> ang_eq E G B G H D \<and> ang_suppl B G H G H D" using Prop29[OF `axioms` `parallel A B C D` `bet A G B` `bet C H D` `bet E G H` `oppo_side A G H D`] .
	have "ang_eq A G H G H D" using `ang_eq A G H G H D \<and> ang_eq E G B G H D \<and> ang_suppl B G H G H D` by blast
	thus ?thesis by blast
qed

end