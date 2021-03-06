theory parallelcollinear1
	imports Geometry NChelper NCorder betweennotequal collinear4 collinear5 collinearbetween collinearorder equalitysymmetric inequalitysymmetric
begin

theorem(in euclidean_geometry) parallelcollinear1:
	assumes 
		"tarski_parallel A B c d"
		"bet C c d"
	shows "tarski_parallel A B C d"
proof -
	have "C \<noteq> c" using betweennotequal[OF `bet C c d`] by blast
	have "c \<noteq> d" using betweennotequal[OF `bet C c d`] by blast
	have "C \<noteq> d" using betweennotequal[OF `bet C c d`] by blast
	have "A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B" using tarski_parallel_f[OF `tarski_parallel A B c d`] .
	have "A \<noteq> B" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
	have "c \<noteq> d" using `c \<noteq> d` .
	have "same_side c d A B" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
	obtain p q r where "col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d" using sameside_f[OF `same_side c d A B`]  by  blast
	have "col A B p" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "col A B r" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "bet c p q" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "bet d r q" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "\<not> col A B c" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "\<not> col A B d" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "bet q r d" using betweennesssymmetryE[OF `bet d r q`] .
	have "col C c d" using collinear_b `bet C c d` by blast
	have "col c d C" using collinearorder[OF `col C c d`] by blast
	have "bet d c C" using betweennesssymmetryE[OF `bet C c d`] .
	have "bet q r d" using `bet q r d` .
	have "bet q p c" using betweennesssymmetryE[OF `bet c p q`] .
	have "\<not> (p = r)"
	proof (rule ccontr)
		assume "\<not> (p \<noteq> r)"
		hence "p = r" by blast
		have "col q r d" using collinear_b `bet q r d` by blast
		have "col q p c" using collinear_b `bet q p c` by blast
		have "col q p d" using `col q r d` `p = r` by blast
		have "q \<noteq> p" using betweennotequal[OF `bet q p c`] by blast
		have "col p c d" using collinear4[OF `col q p c` `col q p d` `q \<noteq> p`] .
		have "col c d p" using collinearorder[OF `col p c d`] by blast
		have "meets A B c d" using meet_b[OF `A \<noteq> B` `c \<noteq> d` `col A B p` `col c d p`] .
		have "\<not> (meets A B c d)" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
		show "False" using `\<not> (meets A B c d)` `meets A B c d` by blast
	qed
	hence "p \<noteq> r" by blast
	have "col q p c" using collinear_b `bet q p c` by blast
	have "\<not> (col q d C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col q d C))"
hence "col q d C" by blast
		have "col d c C" using collinear_b `bet d c C` by blast
		have "col C d c" using collinearorder[OF `col C c d`] by blast
		have "col C d q" using collinearorder[OF `col q d C`] by blast
		have "C \<noteq> d" using betweennotequal[OF `bet C c d`] by blast
		have "col d c q" using collinear4[OF `col C d c` `col C d q` `C \<noteq> d`] .
		have "col c q d" using collinearorder[OF `col d c q`] by blast
		have "col c q p" using collinearorder[OF `col q p c`] by blast
		have "q \<noteq> c" using betweennotequal[OF `bet q p c`] by blast
		have "c \<noteq> q" using inequalitysymmetric[OF `q \<noteq> c`] .
		have "col q d p" using collinear4[OF `col c q d` `col c q p` `c \<noteq> q`] .
		have "col q r d" using collinear_b `bet q r d` by blast
		have "col q d r" using collinearorder[OF `col q r d`] by blast
		have "q \<noteq> d" using betweennotequal[OF `bet q r d`] by blast
		have "col d p r" using collinear4[OF `col q d p` `col q d r` `q \<noteq> d`] .
		have "col A B p" using `col A B p` .
		have "col A B r" using `col A B r` .
		have "col B p r" using collinear4[OF `col A B p` `col A B r` `A \<noteq> B`] .
		have "col B A p" using collinearorder[OF `col A B p`] by blast
		have "col B p A" using collinearorder[OF `col A B p`] by blast
		have "col B A r" using collinearorder[OF `col A B r`] by blast
		have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
		have "col A p r" using collinear4[OF `col B A p` `col B A r` `B \<noteq> A`] .
		have "\<not> (B \<noteq> p)"
		proof (rule ccontr)
			assume "\<not> (\<not> (B \<noteq> p))"
hence "B \<noteq> p" by blast
			have "col p r A" using collinear4[OF `col B p r` `col B p A` `B \<noteq> p`] .
			have "col p r d" using collinearorder[OF `col d p r`] by blast
			have "col r A d" using collinear4[OF `col p r A` `col p r d` `p \<noteq> r`] .
			have "col r A B" using collinearorder[OF `col A B r`] by blast
			have "\<not> (r \<noteq> A)"
			proof (rule ccontr)
				assume "\<not> (\<not> (r \<noteq> A))"
hence "r \<noteq> A" by blast
				have "col A d B" using collinear4[OF `col r A d` `col r A B` `r \<noteq> A`] .
				have "col A B d" using collinearorder[OF `col A d B`] by blast
				have "\<not> col A B d" using `\<not> col A B d` .
				show "False" using `\<not> col A B d` `col A B d` by blast
			qed
			hence "r = A" by blast
			have "col p A d" using `col p r d` `r = A` by blast
			have "col p A B" using collinearorder[OF `col A B p`] by blast
			have "\<not> (p \<noteq> A)"
			proof (rule ccontr)
				assume "\<not> (\<not> (p \<noteq> A))"
hence "p \<noteq> A" by blast
				have "col A d B" using collinear4[OF `col p A d` `col p A B` `p \<noteq> A`] .
				have "col A B d" using collinearorder[OF `col A d B`] by blast
				show "False" using `col A B d` `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
			qed
			hence "p = A" by blast
			have "r = p" using equalitytransitiveE[OF `r = A` `p = A`] .
			have "col q p c" using `col q p c` .
			have "col q r d" using `col q r d` .
			have "col q p d" using `col q r d` `r = p` by blast
			have "q \<noteq> p" using betweennotequal[OF `bet q p c`] by blast
			have "col p c d" using collinear4[OF `col q p c` `col q p d` `q \<noteq> p`] .
			have "col c d p" using collinearorder[OF `col p c d`] by blast
			have "meets A B c d" using meet_b[OF `A \<noteq> B` `c \<noteq> d` `col A B p` `col c d p`] .
			have "\<not> (meets A B c d)" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
			show "False" using `\<not> (meets A B c d)` `meets A B c d` by blast
		qed
		hence "B = p" by blast
		have "col r A B" using collinearorder[OF `col A B r`] by blast
		have "col d B r" using `col d p r` `B = p` by blast
		have "col r B d" using collinearorder[OF `col d B r`] by blast
		have "col r B A" using collinearorder[OF `col A B r`] by blast
		have "\<not> (r \<noteq> B)"
		proof (rule ccontr)
			assume "\<not> (\<not> (r \<noteq> B))"
hence "r \<noteq> B" by blast
			have "col B d A" using collinear4[OF `col r B d` `col r B A` `r \<noteq> B`] .
			have "col A B d" using collinearorder[OF `col B d A`] by blast
			show "False" using `col A B d` `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
		qed
		hence "r = B" by blast
		have "p = B" using equalitysymmetric[OF `B = p`] .
		have "p = r" using equalitytransitiveE[OF `p = B` `r = B`] .
		have "p \<noteq> r" using `p \<noteq> r` .
		show "False" using `p \<noteq> r` `p = r` by blast
	qed
	hence "\<not> col q d C" by blast
	obtain E where "bet q E c \<and> bet C E r" using Pasch_innerE[OF `bet q r d` `bet C c d` `\<not> col q d C`]  by  blast
	have "bet q E c" using `bet q E c \<and> bet C E r` by blast
	have "col q E c" using collinear_b `bet q E c \<and> bet C E r` by blast
	have "col q c p" using collinearorder[OF `col q p c`] by blast
	have "col q c E" using collinearorder[OF `col q E c`] by blast
	have "q \<noteq> c" using betweennotequal[OF `bet q E c`] by blast
	have "col c p E" using collinear4[OF `col q c p` `col q c E` `q \<noteq> c`] .
	have "r \<noteq> p" using inequalitysymmetric[OF `p \<noteq> r`] .
	obtain J where "bet r p J \<and> seg_eq p J r p" using extensionE[OF `r \<noteq> p` `r \<noteq> p`]  by  blast
	have "bet r p J" using `bet r p J \<and> seg_eq p J r p` by blast
	have "bet J p r" using betweennesssymmetryE[OF `bet r p J`] .
	have "col J p r" using collinear_b `bet J p r` by blast
	have "J \<noteq> r" using betweennotequal[OF `bet J p r`] by blast
	have "p \<noteq> r" using betweennotequal[OF `bet J p r`] by blast
	have "J \<noteq> p" using betweennotequal[OF `bet J p r`] by blast
	have "bet C E r" using `bet q E c \<and> bet C E r` by blast
	have "col A B p" using `col A B p` .
	have "col A B r" using `col A B r` .
	have "col B p r" using collinear4[OF `col A B p` `col A B r` `A \<noteq> B`] .
	have "col B A p" using collinearorder[OF `col A B p`] by blast
	have "col B A r" using collinearorder[OF `col A B r`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	have "col A p r" using collinear4[OF `col B A p` `col B A r` `B \<noteq> A`] .
	have "col p r A" using collinearorder[OF `col A p r`] by blast
	have "col p r B" using collinearorder[OF `col B p r`] by blast
	have "\<not> (meets C d J r)"
	proof (rule ccontr)
		assume "\<not> (\<not> (meets C d J r))"
hence "meets C d J r" by blast
		obtain K where "C \<noteq> d \<and> J \<noteq> r \<and> col C d K \<and> col J r K" using meet_f[OF `meets C d J r`]  by  blast
		have "C \<noteq> d" using `C \<noteq> d` .
		have "J \<noteq> r" using `J \<noteq> r` .
		have "col C d K" using `C \<noteq> d \<and> J \<noteq> r \<and> col C d K \<and> col J r K` by blast
		have "col J r K" using `C \<noteq> d \<and> J \<noteq> r \<and> col C d K \<and> col J r K` by blast
		have "col C c d" using collinear_b `bet C c d` by blast
		have "col C d c" using collinearorder[OF `col C c d`] by blast
		have "c \<noteq> d" using betweennotequal[OF `bet C c d`] by blast
		have "d \<noteq> c" using inequalitysymmetric[OF `c \<noteq> d`] .
		have "col d c K" using collinear4[OF `col C d c` `col C d K` `C \<noteq> d`] .
		have "col c d K" using collinearorder[OF `col d c K`] by blast
		have "col r J p" using collinearorder[OF `col J p r`] by blast
		have "r \<noteq> J" using betweennotequal[OF `bet r p J`] by blast
		have "col r J K" using collinearorder[OF `col J r K`] by blast
		have "col J p K" using collinear4[OF `col r J p` `col r J K` `r \<noteq> J`] .
		have "col J p r" using collinearorder[OF `col r J p`] by blast
		have "p \<noteq> J" using betweennotequal[OF `bet r p J`] by blast
		have "J \<noteq> p" using inequalitysymmetric[OF `p \<noteq> J`] .
		have "col p K r" using collinear4[OF `col J p K` `col J p r` `J \<noteq> p`] .
		have "col p r K" using collinearorder[OF `col p K r`] by blast
		have "col p r A" using `col p r A` .
		have "col p r B" using `col p r B` .
		have "col A B K" using collinear5[OF `p \<noteq> r` `col p r A` `col p r B` `col p r K`] .
		have "meets A B c d" using meet_b[OF `A \<noteq> B` `c \<noteq> d` `col A B K` `col c d K`] .
		have "\<not> (meets A B c d)" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
		show "False" using `\<not> (meets A B c d)` `meets A B c d` by blast
	qed
	hence "\<not> (meets C d J r)" by blast
	have "bet c E p" using collinearbetween[OF `col C c d` `col J p r` `C \<noteq> d` `J \<noteq> r` `C \<noteq> c` `p \<noteq> r` `\<not> (meets C d J r)` `bet C E r` `col c p E`] .
	have "bet p E c" using betweennesssymmetryE[OF `bet c E p`] .
	have "bet q p E" using innertransitivityE[OF `bet q p c` `bet p E c`] .
	have "p \<noteq> r" using `p \<noteq> r` .
	have "\<not> col p r c" using NChelper[OF `\<not> col A B c` `col A B p` `col A B r` `p \<noteq> r`] .
	have "\<not> col p c r" using NCorder[OF `\<not> col p r c`] by blast
	have "col q p c" using collinear_b `bet q p c` by blast
	have "col p c q" using collinearorder[OF `col q c p`] by blast
	have "c = c" using equalityreflexiveE.
	have "col p c c" using collinear_b `c = c` by blast
	have "q \<noteq> c" using betweennotequal[OF `bet q E c`] by blast
	have "\<not> col q c r" using NChelper[OF `\<not> col p c r` `col p c q` `col p c c` `q \<noteq> c`] .
	have "\<not> col q r c" using NCorder[OF `\<not> col q c r`] by blast
	have "q \<noteq> d" using betweennotequal[OF `bet q r d`] by blast
	have "q = q" using equalityreflexiveE.
	have "col d c C" using collinearorder[OF `col C c d`] by blast
	have "C \<noteq> d" using betweennotequal[OF `bet C c d`] by blast
	have "d \<noteq> C" using inequalitysymmetric[OF `C \<noteq> d`] .
	have "\<not> col d q C" using NCorder[OF `\<not> col q d C`] by blast
	have "col q r d" using collinear_b `bet q r d` by blast
	have "col d q r" using collinearorder[OF `col q r d`] by blast
	have "col d q q" using collinear_b `q = q` by blast
	have "\<not> (r = C)"
	proof (rule ccontr)
		assume "\<not> (r \<noteq> C)"
		hence "r = C" by blast
		have "col c d C" using `col c d C` .
		have "col A B r" using `col A B r` .
		have "col A B C" using `col A B r` `r = C` by blast
		have "meets A B c d" using meet_b[OF `A \<noteq> B` `c \<noteq> d` `col A B C` `col c d C`] .
		have "\<not> (meets A B c d)" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
		show "False" using `\<not> (meets A B c d)` `meets A B c d` by blast
	qed
	hence "r \<noteq> C" by blast
	have "\<not> (r = q)"
	proof (rule ccontr)
		assume "\<not> (r \<noteq> q)"
		hence "r = q" by blast
		have "col r q c" using collinear_b `r = q` by blast
		have "col q r c" using collinearorder[OF `col r q c`] by blast
		show "False" using `col q r c` `\<not> col q r c` by blast
	qed
	hence "r \<noteq> q" by blast
	have "\<not> col r q C" using NChelper[OF `\<not> col d q C` `col d q r` `col d q q` `r \<noteq> q`] .
	have "\<not> col r C q" using NCorder[OF `\<not> col r q C`] by blast
	have "bet r E C" using betweennesssymmetryE[OF `bet C E r`] .
	have "bet q p E" using `bet q p E` .
	obtain F where "bet q F C \<and> bet r p F" using Pasch_outerE[OF `bet q p E` `bet r E C` `\<not> col r C q`]  by  blast
	have "bet q F C" using `bet q F C \<and> bet r p F` by blast
	have "bet C F q" using betweennesssymmetryE[OF `bet q F C`] .
	have "bet r p F" using `bet q F C \<and> bet r p F` by blast
	have "col r p F" using collinear_b `bet q F C \<and> bet r p F` by blast
	have "col r p A" using collinearorder[OF `col A p r`] by blast
	have "col r p B" using collinearorder[OF `col B p r`] by blast
	have "col A B F" using collinear5[OF `r \<noteq> p` `col r p A` `col r p B` `col r p F`] .
	have "\<not> col q C r" using NCorder[OF `\<not> col r C q`] by blast
	have "col q F C" using collinear_b `bet q F C \<and> bet r p F` by blast
	have "col q C F" using collinearorder[OF `col q F C`] by blast
	have "C = C" using equalityreflexiveE.
	have "col q C C" using collinear_b `C = C` by blast
	have "F \<noteq> C" using betweennotequal[OF `bet q F C`] by blast
	have "\<not> col F C r" using NChelper[OF `\<not> col q C r` `col q C F` `col q C C` `F \<noteq> C`] .
	have "\<not> col F r C" using NCorder[OF `\<not> col F C r`] by blast
	have "col A B r" using `col A B r` .
	have "col A B p" using `col A B p` .
	have "col p r A" using collinearorder[OF `col A p r`] by blast
	have "col p r F" using collinearorder[OF `col r p F`] by blast
	have "p \<noteq> r" using betweennotequal[OF `bet J p r`] by blast
	have "col r A F" using collinear4[OF `col p r A` `col p r F` `p \<noteq> r`] .
	have "col F r A" using collinearorder[OF `col r A F`] by blast
	have "col B A r" using collinearorder[OF `col A B r`] by blast
	have "col B A p" using collinearorder[OF `col A B p`] by blast
	have "col A B r" using collinearorder[OF `col B A r`] by blast
	have "col A B p" using collinearorder[OF `col B A p`] by blast
	have "col p r B" using collinearorder[OF `col B p r`] by blast
	have "col r B F" using collinear4[OF `col p r B` `col p r F` `p \<noteq> r`] .
	have "col F r B" using collinearorder[OF `col r B F`] by blast
	have "\<not> col A B C" using NChelper[OF `\<not> col F r C` `col F r A` `col F r B` `A \<noteq> B`] .
	have "same_side C d A B" using sameside_b[OF `col A B F` `col A B r` `bet C F q` `bet d r q` `\<not> col A B C` `\<not> col A B d`] .
	have "\<not> (meets A B C d)"
	proof (rule ccontr)
		assume "\<not> (\<not> (meets A B C d))"
hence "meets A B C d" by blast
		obtain K where "A \<noteq> B \<and> C \<noteq> d \<and> col A B K \<and> col C d K" using meet_f[OF `meets A B C d`]  by  blast
		have "A \<noteq> B" using `A \<noteq> B` .
		have "col A B K" using `A \<noteq> B \<and> C \<noteq> d \<and> col A B K \<and> col C d K` by blast
		have "col C d K" using `A \<noteq> B \<and> C \<noteq> d \<and> col A B K \<and> col C d K` by blast
		have "col C d c" using collinearorder[OF `col C c d`] by blast
		have "C \<noteq> d" using betweennotequal[OF `bet C c d`] by blast
		have "col d c K" using collinear4[OF `col C d c` `col C d K` `C \<noteq> d`] .
		have "col c d K" using collinearorder[OF `col d c K`] by blast
		have "meets A B c d" using meet_b[OF `A \<noteq> B` `c \<noteq> d` `col A B K` `col c d K`] .
		have "\<not> (meets A B c d)" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
		show "False" using `\<not> (meets A B c d)` `meets A B c d` by blast
	qed
	hence "\<not> (meets A B C d)" by blast
	have "C \<noteq> d" using betweennotequal[OF `bet C c d`] by blast
	have "tarski_parallel A B C d" using tarski_parallel_b[OF `A \<noteq> B` `C \<noteq> d` `\<not> (meets A B C d)` `same_side C d A B`] .
	thus ?thesis by blast
qed

end