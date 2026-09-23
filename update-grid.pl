#!/usr/bin/perl
# update the grid from the sorted list in README.md and
# crosscheck with the tests if it is stable (x), not yet implemented () or still
# broken (.).

use strict;
use utf8;
use feature 'unicode_strings';
binmode(STDOUT, ":utf8");

open my $in, '<:utf8', 'README.md' or die "$! README.md";
my @c1 = qw(vec str arr deq list slst pqu que stk bvec btst span strv ivec hive);
my @c2 = qw(set map uset umap fset fmap swiss hmap);
my @c = (@c1, @c2);
my %long = (
  vec => 'vector',
  str => 'string',
  arr => 'array',
  deq => 'deque',
  list => 'list',
  slst => 'forward_list',
  set => 'set',
  map => 'map',
  uset => 'unordered_set',
  umap => 'unordered_map',
  pqu => 'priority_queue',
  que => 'queue',
  stk => 'stack',
  bvec => 'bvector',
  btst => 'btree_set',
  span => 'span',
  strv => 'strv',
  fset => 'flat_set',
  fmap => 'flat_map',
  ivec => 'inplace_vector',
  hive => 'hive',
  swiss => 'swisstable',
  hmap => 'hashmap',
);
# per-column display width (cells use one leading space + content)
my %W = map { $_ => length($_) < 4 ? 4 : length($_) } @c;
# containers whose default methods differ from the classic set
my %no_common = (
  bvec => [qw(init_from equal)],
  span => [qw(init_from equal)],
  strv => [qw(init_from)],
  btst => [qw(equal)],
  ivec => [qw(equal)],
  hive => [qw(equal)],
  swiss => [qw(init_from equal)],
  hmap => [qw(init_from equal)],
);
my $m = {};

my (@methods, @n);


# check all tests for its status
sub status {
  my ($c,$f) = @_;
  open my $in, '<', $f or die "$! $f";
  my ($status, %seen);
  my $has_foreach = 0;
  while (<$in>) {
    if (/^#define FOREACH_METH/) {
      $has_foreach = 1;
      $status = '✓';
    }
    elsif (/^#define FOREACH_DEBUG/) {
      $status = 'x';
    }
    #elsif (/^#define GENERATE_ENUM/) {
    #  close $in;
    #  return;
    #}
    elsif (/^\s+TEST\((\w+)\)/) {
      my $n = $1;
      my $l = lc $n;
      next if $n eq 'SELF';
      warn "overwrite undefined $c.$l -" if $m->{$l}->{$c} eq '-';
      $m->{$l}->{$c} = $status;
    }
    elsif (/^\s+case TEST_(\w+):/) {
      my $l = lc $1;
      warn "seen undefined $c.$l -" if $m->{$l}->{$c} eq '-';
      $seen{$l}++;
    }
  }
  close $in;
  # no FOREACH_* enumeration (plain .c regression test): the %impl table
  # below carries this container's status instead.
  return unless $has_foreach;
  my @keys = keys %{$m->{$c}};
  foreach (@keys) {
    # check if the test case is defined or not
    next if $m->{$_}->{$c} eq '✓';
    next if $m->{$_}->{$c} eq '-';
    if (!exists $seen{$_}) {
      warn "No test yet for $c.$_ \n" if $m->{$_}->{$c} eq 'x';
      $m->{$_}->{$c} = '';
    }
  }
}

for (keys %long) {
  my $f = "tests/func/test_" . $long{$_} . ".cc";
  $f = "tests/func/test_" . $long{$_} . ".c" unless -e $f;
  die "no $f $!" unless -e $f;
  status($_,$f);
}

# add common methods, untested per se
for my $c (@c) {
  for my $meth (qw(init init_from free equal size max_size empty)) {
    next if grep { $_ eq $meth } @{$no_common{$c} || []};
    $m->{$meth}->{$c} = '✓';
  }
}
$m->{compare}->{str} = '✓';
$m->{key_compare}->{str} = '✓';
$m->{erase_node}->{list} = '✓';
$m->{erase_node}->{set} = '✓';
for my $c (qw(vec str arr deq list slst set map uset umap
              btst fset fmap ivec hive swiss hmap)) {
  for (qw(begin end next foreach ref)) {
    $m->{$_}->{$c} = '✓';
  }
  $m->{inserter}->{$c} = $m->{copy_if}->{$c};
}
# contiguous/bidirectional iterators without next/ref
for my $c (qw(span)) {
  for (qw(begin end foreach)) {
    $m->{$_}->{$c} = '✓';
  }
}
for my $c (qw(vec str arr deq list slst set map)) {
  for (qw(advance distance range foreach_range foreach_n foreach_n_range)) {
    $m->{$_}->{$c} = '✓';
  }
  $m->{distance_range}->{$c} = $m->{lower_bound_range}->{$c};
  # union tests copy_range
  if ($c ne 'set' and $c ne 'map') {
    $m->{copy_range}->{$c} = $m->{union}->{$c};
  }
  if ($c =~ /list/) {
    $m->{iter_swap}->{$c} = $m->{shuffle}->{$c};
  } else {
    $m->{iter_swap}->{$c} = $m->{reverse}->{$c};
  }
}
for my $c (qw(ivec)) {
  for (qw(advance advance_end distance range)) {
    $m->{$_}->{$c} = '✓';
  }
}
for my $c (qw(uset umap swiss hmap)) {
  for (qw(load_factor max_load_factor)) {
    $m->{$_}->{$c} = '✓';
  }
  # no bucket interface on the open-addressing tables
  if ($c eq 'swiss' or $c eq 'hmap') {
    for (qw(max_bucket_count bucket_count bucket_size)) {
      $m->{$_}->{$c} = '-' if exists $m->{$_};
    }
  }
  # undefined iter methods
  for (qw(advance advance_end distance distance_range range foreach_range foreach_n foreach_n_range)) {
    $m->{$_}->{$c} = '-' if exists $m->{$_};
  }
}

# Containers without a FOREACH_* STL-differential test (plain .c
# regression tests, or fixed-name headers like bvec/strv): status
# derived from the methods implemented in ctl/<long>.h, and whether
# tests/func/test_<long>.[cc] exercises them. Refresh by hand when
# adding methods. Keys not matching a grid row are ignored.
my %impl = (
  bvec => [qw(init free size empty at capacity reserve set data push pop clear)],
  btst => [qw(init init_from free copy size empty begin end next ref at back front insert erase contains count clear swap)],
  span => [qw(init empty at back front begin end data)],
  strv => [qw(init empty size at back front begin end data find compare equal)],
  fset => [qw(init free size empty begin end next ref contains count erase find insert lower_bound upper_bound equal_range)],
  fmap => [qw(init free size empty begin end next ref contains count erase find insert lower_bound upper_bound equal_range insert_or_assign insert_or_assign_found)],
  ivec => [qw(init init_from free copy size max_size empty begin end next ref advance advance_end distance range at back front data capacity push_back pop_back insert insert_index erase erase_index erase_range resize assign clear sort find remove_if erase_if emplace_back swap try_push_back)],
  hive => [qw(init init_from free copy size max_size empty begin end next ref contains count insert erase erase_it emplace find clear remove_if erase_if capacity reserve swap)],
  swiss => [qw(init free size empty max_size begin end next ref foreach find contains insert erase clear copy assign swap count equal_range load_factor max_load_factor rehash reserve)],
  hmap => [qw(init init_with free size empty max_size begin end next ref foreach find contains insert erase clear copy assign swap count equal_range load_factor max_load_factor rehash reserve)],
);
my %tested = (
  bvec => [qw(init free size empty at push pop set)],
  btst => [qw(init init_from free copy size empty begin end next ref at back front insert erase contains count clear swap)],
  span => [qw(init empty at back front begin end data)],
  strv => [qw(init empty size at back front begin end data find compare equal)],
  fset => [qw(init free size empty begin end next ref contains count erase find insert lower_bound upper_bound equal_range)],
  fmap => [qw(init free size empty begin end next ref contains count erase find insert lower_bound upper_bound equal_range insert_or_assign)],
  ivec => [qw(init init_from free copy size max_size empty begin end next ref at back front data capacity push_back pop_back insert insert_index erase erase_index erase_range resize assign clear sort find remove_if erase_if emplace_back swap try_push_back)],
  hive => [qw(init init_from free copy size max_size empty begin end next ref contains count insert erase erase_it emplace find clear remove_if erase_if capacity reserve swap)],
  swiss => [qw(init free size empty max_size begin end next ref foreach find contains insert erase clear copy assign swap count equal_range load_factor max_load_factor reserve)],
  hmap => [qw(init free size empty max_size begin end next ref foreach find contains insert erase clear copy assign swap count equal_range load_factor max_load_factor reserve)],
);
for my $c (keys %impl) {
  my %t = map { $_ => 1 } @{$tested{$c}};
  for my $meth (@{$impl{$c}}) {
    $m->{$meth}->{$c} = $t{$meth} ? '✓' : 'x';
  }
}
# cells for the new containers on rows they don't implement stay blank
for my $c (keys %impl) {
  for my $row (grep { ref $m->{$_} eq 'HASH' } keys %$m) {
    $m->{$row}->{$c} = '' unless defined $m->{$row}->{$c};
  }
}

# layout:
#   5 space for the col
my $M = 31; # longest method name

my ($countok, $countm);


sub print_table {
  my (@cols) = @_;
  my $s = "|" . ' ' x ($M + 2);
  for (@cols) {
    $s .= sprintf("|%-*s ", $W{$_}, $_);
  }
  $s .= "|\n";
  printf $s;
  push @n, $s;
  my $s = "|" . '-' x ($M + 2);
  for (@cols) {
    $s .= "|" . '-' x $W{$_} . ' ';
  }
  $s .= "|\n";
  printf $s;
  push @n, $s;
  for (@methods) {
    my $L = $M - length($_);
    my $s = sprintf("|`%s`%s", $_, ' ' x $L);
    for my $c (@cols) {
      my $x = $m->{$_}->{$c};
      $countok++ if $x eq '✓';
      $x = '' unless $x;
      $s .= sprintf "| %-*s ", $W{$c} - 1, $x;
    }
    $countm++ if $s =~ /✓/;
    $s .= "|\n";
    printf $s;
    push @n, $s;
    if (/^(key_compare|range|lexicographical_compare)$/) {
      my $s = "|" . '-' x ($M + 2);
      for (@cols) {
        $s .= "|" . '-' x $W{$_} . ' ';
      }
      $s .= "|\n";
      printf $s;
      push @n, $s;
      my $s = "|" . ' ' x ($M + 2);
      for (@cols) {
        $s .= sprintf("|%-*s ", $W{$_}, $_);
      }
      $s .= "|\n";
      printf $s;
      push @n, $s;
      my $s = "|" . '-' x ($M + 2);
      for (@cols) {
        $s .= "|" . '-' x $W{$_} . ' ';
      }
      $s .= "|\n";
      printf $s;
      push @n, $s;
    }
  }
  my $s = "|" . '-' x ($M + 2);
  for (@cols) {
    $s .= "|" . '-' x $W{$_} . ' ';
  }
  $s .= "|\n";
  printf $s;
  push @n, $s;
}

# print grid
@methods = sort keys %$m;
print_table(@c1);
push @n, "\n";
print "\n";
print_table(@c2);
push @n, "\n";
print "\n";

sub update {
  my $found = 0;
  open my $in, '<:utf8', 'README.md' or die "$! README.md";
  open my $out, '>:utf8', 'README.md.tmp' or die "$! README.md.tmp";
  while (<$in>) {
    if (/We have \d* methods in \d* stable variants/) {
      s{We have \d* methods in \d* stable variants}
       {We have $countm methods in $countok stable variants};
    }
    if (!$found and /^\|\s+\|vec\s+\|str\s+\|arr\s+\|deq/) {
      $found = 1;
      for (@n) {
        s/ +$//;
        print $out $_;
      }
      @n = ();
      next;
    }
    if ($found) {
      if (/^## Differences/) {
        $found = 0;
      } else {
        next;
      }
    }
    print $out $_;
  }
  close $in;
  close $out;
  system("mv README.md.tmp README.md");
  system("./update-index.pl");
}

update();
