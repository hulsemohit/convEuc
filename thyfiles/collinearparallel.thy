theory collinearparallel
	imports Geometry collinear4 collinearorder
begin

theorem(in euclidean_geometry) collinearparallel:
	assumes 
		"parallel A B c d"
		"col c d C"
		"C \<noteq> d"
	shows "parallel A B C d"
proof -
	obtain R a b p q where "A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b" using parallel_f[OF `parallel A B c d`]  by  blast
	have "A \<noteq> B" using `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` by blast
	have "c \<noteq> d" using `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` by blast
	have "col A B a" using `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` by blast
	have "col A B b" using `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` by blast
	have "a \<noteq> b" using `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` by blast
	have "col c d q" using `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` by blast
	have "p \<noteq> q" using `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` by blast
	have "\<not> (meets A B c d)" using `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` by blast
	have "bet a R q" using `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` by blast
	have "bet p R b" using `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` by blast
	have "col c d p" using `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` by blast
	have "col d C p" using collinear4[OF `col c d C` `col c d p` `c \<noteq> d`] .
	have "col C d p" using collinearorder[OF `col d C p`] by blast
	have "col d C q" using collinear4[OF `col c d C` `col c d q` `c \<noteq> d`] .
	have "col C d q" using collinearorder[OF `col d C q`] by blast
	have "\<not> (meets A B C d)"
	proof (rule ccontr)
		assume "\<not> (\<not> (meets A B C d))"
hence "meets A B C d" by blast
		obtain E where "A \<noteq> B \<and> C \<noteq> d \<and> col A B E \<and> col C d E" using meet_f[OF `meets A B C d`]  by  blast
		have "col A B E" using `A \<noteq> B \<and> C \<noteq> d \<and> col A B E \<and> col C d E` by blast
		have "col C d E" using `A \<noteq> B \<and> C \<noteq> d \<and> col A B E \<and> col C d E` by blast
		have "col C d c" using collinearorder[OF `col c d C`] by blast
		have "col d E c" using collinear4[OF `col C d E` `col C d c` `C \<noteq> d`] .
		have "col c d E" using collinearorder[OF `col d E c`] by blast
		have "A \<noteq> B \<and> c \<noteq> d \<and> col A B E \<and> col c d E" using `A \<noteq> B \<and> C \<noteq> d \<and> col A B E \<and> col C d E` `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` `A \<noteq> B \<and> C \<noteq> d \<and> col A B E \<and> col C d E` `col c d E` by blast
		have "meets A B c d" using meet_b[OF `A \<noteq> B` `c \<noteq> d` `col A B E` `col c d E`] .
		show "False" using `meets A B c d` `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` by blast
	qed
	hence "\<not> (meets A B C d)" by blast
	have "A \<noteq> B \<and> C \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C d p \<and> col C d q \<and> p \<noteq> q \<and> \<not> (meets A B C d) \<and> bet a R q \<and> bet p R b" using `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` `C \<noteq> d` `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` `col C d p` `col C d q` `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` `\<not> (meets A B C d)` `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` `A \<noteq> B \<and> c \<noteq> d \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col c d p \<and> col c d q \<and> p \<noteq> q \<and> \<not> (meets A B c d) \<and> bet a R q \<and> bet p R b` by blast
	have "parallel A B C d" using parallel_b[OF `A \<noteq> B` `C \<noteq> d` `col A B a` `col A B b` `a \<noteq> b` `col C d p` `col C d q` `p \<noteq> q` `\<not> (meets A B C d)` `bet a R q` `bet p R b`] .
	thus ?thesis by blast
qed

end