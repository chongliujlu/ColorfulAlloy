/**
  **   POSIX (Portable Opearting System Interface of UNIX) file system 

  **   partition （base）file system  ➀， block ➁， create ➂， list➃，Move➄，Remove ➅ Symbolic links➆
                                                    
				          (abstract) Inode  
                                                            /           \
                                      (abstract) composite    File
                                                         /  \
                                                     Dir     SymLink➆
*/
 
module filesystem

// allocation map = partition = file system - central file system allocation map needed for alloy
sig AMap {
	designation: one Device,
	➀root: one Dir➀,
	➀objects: set Inode➀,
	➀contents: Composite lone-> Inode➀,
	➀parent: Inode ->lone Dir➀,
	➁datablocks: some Block➁ // blocks inside this partition available for keeping data
	} 

abstract sig Device {
	➁blocks: disj some Block➁
	}
one sig Dev0, Dev1, Dev2 extends Device {}

➁sig Block { }➁

fact Blocks_fact {
	➁all m: AMap | m.datablocks in m.designation.blocks➁
}

// File system objects
➀abstract sig Inode {} {
	// all Inodes must have a parent (no Inodes belonging to no FS)
	all n: Inode | n in AMap.objects
	}➀

➀sig File extends Inode {
	// essentially these are the file's clusters
	➁contents: disj some Block➁
	}➀

fact FSBlocks_fact {
	➁➀all m:AMap, f: (File&m.objects) | f.contents in m.datablocks ➀➁// all file contents of this file system are inside this partition
}

➀abstract sig Composite extends Inode { }➀ // directory contents needed at top level

➀sig Dir extends Composite {}➀

fact FS_fact {
	// root has no parent
	➀all m:AMap | no m.root.(m.parent)➀
	// objects are those reachable from directories, starting at root
	➀all m:AMap | m.objects = m.root.*(Dir <: m.contents)➀
	// contents only defined on objects
	➀all m:AMap | m.contents in m.objects->Inode➀
	// parent is the inverse of contents
	➀all m:AMap, d: Dir, n: Inode | n in (d.(m.contents)) => n.(m.parent) = d➀
}


// These are two different partitions on the same system
pred disjointPartitions[fs1, fs2: AMap] {
	fs1.designation != fs2.designation
	➀fs1.root != fs2.root➀
	➀#(fs1.objects&fs2.objects) = 0➀	
	}

// All file systems are disjoint (they might coexist on the same machine)
pred allDisjointPartitions {
	all disj fs1, fs2: AMap | disjointPartitions[fs1, fs2]
}

/*-- ???? disj in ExprQt 
--Is it not same with  
	"run disjointPartitions with exactly ➀ for 6 but 3 AMap"  adding "disj" keyword
		 to disjointPartitions's parameter?*/
run allDisjointPartitions with exactly ➀ for 6 but 3 AMap
run allDisjointPartitions with  ➀ for 6 but 3 AMap

// Two file systems represent the same partition, but may have different contents (used for operations on Inodes)
pred changedFS[fs1, fs2: AMap] {
	fs1 != fs2
	fs1.designation = fs2.designation
	➀fs1.root =fs2.root➀
	➀fs1.contents!=fs2.contents➀
	➁fs1.datablocks = fs2.datablocks➁
}
run changedFS with exactly ➀for 6 but exactly 2 AMap
run changedFS with exactly ➁for 6 but exactly 2 AMap
--run changedFS with  ➀for 6 but exactly 2 AMap


assert changingFSChangesContentsNotPartition {
	all fs1, fs2: AMap | changedFS[fs1, fs2] => ➀fs1.contents != fs2.contents ➀ &&➁fs1.datablocks = fs2.datablocks➁

}
check changingFSChangesContentsNotPartition with exactly ➀ for 5 but 2 AMap
check changingFSChangesContentsNotPartition with exactly ➁ for 5 but 2 AMap
check changingFSChangesContentsNotPartition with exactly ➀,➁ for 5 but 2 AMap

--check changingFSChangesContentsNotPartition with  ➀ for 5 but 2 AMap


// Two file systems represent the same contents, but may reside on different devices (used for physical operations)
pred changedPartition[fs1, fs2: AMap] {
	fs1 != fs2
	fs1.designation != fs2.designation
	➀fs1.root =fs2.root➀
	➀fs1.contents=fs2.contents➀
	➁fs1.datablocks != fs2.datablocks➁
}
run changedPartition with exactly➀ for 6 but exactly 2 AMap
run changedPartition with ➀ for 6 but exactly 2 AMap


assert changingPartitiondoesNotChangeFSChangeBlocks {
	all fs1, fs2: AMap | changedPartition[fs1, fs2] => ➀fs1.root = fs2.root➀ &&
							    ➀ fs1.contents = fs2.contents➀ &&
							    ➁fs1.datablocks != fs2.datablocks➁
}
check changingPartitiondoesNotChangeFSChangeBlocks with exactly ➀ for 5 but 2 AMap
check changingPartitiondoesNotChangeFSChangeBlocks with exactly ➁ for 5 but 2 AMap
check changingPartitiondoesNotChangeFSChangeBlocks with exactly ➀,➁ for 5 but 2 AMap
check changingPartitiondoesNotChangeFSChangeBlocks with ➀ for 5 but  2 AMap

// count used blocks
fun du[fs: AMap]: one Int {
	➀➁#((fs.objects&File).contents)➁➀
}

// count free blocks
fun df [fs: AMap]: one Int {
	➀➁#(fs.datablocks) - du[fs]➁➀
}

pred fsWithFreeBlocks(fs: AMap) {
	➀➁df[AMap] > 0➁➀
}

// each block may belong to only one file
assert noSharedBlocks {
	➀➁no disj f1, f2: File | #(f1.contents & f2.contents) > 0➁➀
}

run fsWithFreeBlocks with exactly ➀,➁ for 5 
check noSharedBlocks with exactly ➀,➁ for 5   

// change the size of a partition
pred partitionResize[fs, fs': AMap] {
	➁#fs.datablocks != #fs'.datablocks➁
	changedPartition[fs, fs'] 
}

// Two file systems represent the same partition, but may have different contents (used for operations on Inodes)
assert resizingDoesNotChangeFS {
	all fs1, fs2: AMap | (
		partitionResize[fs1, fs2] =>
		➀fs1.root = fs2.root➀ &&
		➀fs1.contents = fs2.contents➀)
}

run partitionResize with exactly ➀,➁ for 5
check resizingDoesNotChangeFS with exactly ➀,➁ for 5 but 2 AMap
--check resizingDoesNotChangeFS with  ➀,➁ for 5 but 2 AMap

pred creat(fs, fs': AMap, ➀cd: ➀Dir➀➀, f: ➀File➀) {
	➂➀cd in fs.objects➀➂
	➂➀!f in (AMap-fs').objects➀➂ // f is new
	➂➀fs'.contents = fs.contents + (cd->f)➀➂
	➂changedFS[fs, fs'] ➂
}

// create (empty) Directory
pred mkdir(disj fs, fs': AMap, cd: ➀Dir➀, dir: ➀Dir➀) {
	➂➀cd in fs.objects➀➂
	➂➀!dir in (AMap-fs').objects ➀➂// dir is new
	➂➀fs'.contents = fs.contents + (cd->dir)➀➂
	➂changedFS[fs, fs'] ➂
}

run creat with exactly ➀,➂for 4 --but 2 AMap, 4 Inode
run mkdir for 4 but 2 AMap, 4 Inode

// Creating a file or a directory adds exactly one Inode
assert creatAddsOneFile {
  ➂all fs, fs': AMap, cd: ➀Dir➀, f: ➀File➀ |
   ➀ creat[fs, fs', cd, f]=> (#fs'.objects =#fs.objects + 1 && fs'.objects = fs.objects + f)➀➂
}

// Creating a file or a directory adds exactly one Inode
assert mkdirAddsOneDir {
 ➂ all fs, fs': AMap, cd: ➀Dir➀, d:➀ Dir➀ |
    ➀mkdir[fs, fs', cd, d]=> (#fs'.objects = #fs.objects +1 && fs'.objects = fs.objects + d)➀➂
}

// creat does not change another existing filesystem
assert creatKeepsDisjointFilesystemsUnchanged {
➂	all fs, fs', fs2: AMap, cd: ➀Dir➀, f:➀ File ➀|
		creat[fs, fs', cd, f] && disjointPartitions[fs, fs2]
		=> changedFS[fs, fs'] && disjointPartitions[fs', fs2]➂
}

// mkdir does not change another existing filesystem
assert mkdirKeepsDisjointFilesystemsUnchanged {
➂	all fs, fs', fs2: AMap, cd: ➀Dir➀, dir: ➀Dir➀ |
		mkdir[fs, fs', cd, dir] && disjointPartitions[fs, fs2]
		=> changedFS[fs, fs'] && disjointPartitions[fs', fs2]➂
}

-- amalgamate method not support
check creatAddsOneFile with exactly ➀,➂ for 5 
check mkdirAddsOneDir with exactly ➀,➂  for 5
check mkdirKeepsDisjointFilesystemsUnchanged with exactly ➀,➂ for 5 
check creatKeepsDisjointFilesystemsUnchanged with exactly ➀,➂for 5 

assert CreatNeedsFreeSpace {
  ➂all fs, fs': AMap, cd: ➀Dir➀, f: ➀File➀ |
    creat[fs, fs', cd, f]=> df[fs] > 0➂
}

// creat reduces the number of free blocks (in this model, every file uses at least one block)
assert creatLessensSpace {
  ➂all fs, fs': AMap, cd: ➀Dir➀, f: ➀File➀ |
    creat[fs, fs', cd, f]=> df[fs'] < df[fs] ➂
}

assert mkdirKeepsDatablocksConstant {
  ➂all fs, fs': AMap, cd: ➀Dir➀, dir: ➀Dir➀ |
    mkdir[fs, fs', cd, dir]=> df[fs'] = df[fs] ➂
}

check CreatNeedsFreeSpace with exactly ➀,➁,➂ for 5   
check creatLessensSpace with exactly ➀,➁,➂ for 5  but 2 AMap  
check mkdirKeepsDatablocksConstant with exactly ➀,➁,➂ for 5 



// find file
fun find [cd: ➀Dir➀, n: ➀Inode➀] : set ➀Inode➀ {
	--➀➃n in cd.*(AMap.contents) => n else 0➃➀ 
	➀➃n in cd.*(Dir<: AMap.contents) => n else 0➃➀
}

// directory listing
fun ls[cd: ➀Dir➀] : set ➀Inode➀ {
	--➃➀cd.(AMap.contents)➀➃
          ➃➀cd.^(Dir <: AMap.contents)➀➃

}

// recursive directory listing
fun ls_r[cd: ➀Dir➀] : set ➀Inode➀ {
	--➃➀cd.^(AMap.contents)➀➃
	➃➀cd.^(Dir <: AMap.contents)➀➃
}

// lists the full path of an Inode; actually, the parent directories are not ordered
fun fullPath[fs: AMap, f: ➀Inode➀]: set ➀Inode➀ {
	➃➀f.^(fs.parent)➀➃
}

// if the searched Inode is in a different file system, then it cannot be found using find
assert unfindableInodes {
	➃➀all disj m1,m2: AMap, cd:Dir&m1.objects, n: m2.objects | disjointPartitions[m1,m2] => no Inode&find[cd, n]➀➃
}

assert ls_doesNotBreakFSboundaries {
	➃➀all disj m1,m2: AMap, cd:Dir&m1.objects | disjointPartitions[m1,m2] => no ls[cd] & m2.objects➀➃
}

assert ls_r_doesNotBreakFSboundaries {
	➃➀all disj m1,m2: AMap, cd:Dir&m1.objects | disjointPartitions[m1,m2] => no ls_r[cd] & m2.objects➀➃
}

check unfindableInodes with exactly ➀,➃ for 5 but 2 AMap
check ls_doesNotBreakFSboundaries with exactly ➀,➃ for 5 but 2 AMap
check ls_r_doesNotBreakFSboundaries with exactly ➀,➃ for 5 but 2 AMap


// Move Inode f to Directory d inside the same filesystem
pred mv (fs, fs': AMap, n: ➀ Inode➀, dir: ➀Dir➀) {
	➄➀n in fs.objects➀➄ // n is part of the file system
	➄➀dir in fs.objects➀➄ // move inside the file system	
	➄➀fs'.contents = fs.contents - n.(fs.parent)->dir + dir->n➀➄
	➄➀changedFS[fs, fs'] ➀➄
}

// Moving doesn't add or delete any file system objects
assert moveAddsRemovesNone {
 ➄➀ all fs, fs': AMap, f: Inode, d:Dir |
    mv[fs, fs', f, d] => fs.objects = fs'.objects➀➄
}

check moveAddsRemovesNone with exactly ➀,➄ for 5 but exactly 2 AMap 

// mv (inside a FS) does not change the storage state of the filesystem
assert mvKeepsStorageStateUnchanged {
 ➄➀➁ all fs, fs': AMap, n: Inode, dir: Dir |
    mv[fs, fs', n, dir]=> fs.datablocks = fs'.datablocks➁➀➄
}

check mvKeepsStorageStateUnchanged with exactly ➀,➁,➄ for 5 


// Delete the file f
pred rm (fs, fs': AMap, f: ➀File➀) {
	➀➅f in fs.objects➅➀
	➀➅fs'.contents = fs.contents - f.(fs.parent)->f➅➀
	➀➅changedFS[fs, fs'] ➅➀
}

// Delete the directory d
pred rmdir(fs, fs': AMap, d: ➀Dir➀) {
	➀➅d in fs.(objects - root)➅➀
	➀➅no d.(fs.contents)➅➀ // d is empty
	➀➅fs'.contents = fs.contents - d.(fs.parent)->d➅➀
	➀➅changedFS[fs, fs'] ➅➀
}

// Recursively delete the file system object f
pred rm_r(fs, fs': AMap, f: ➀Inode➀) {
	➀➅f in fs.(objects - root)➅➀
	➀➅let subtree = f.*(fs.contents) |
 		fs'.contents = fs.contents - subtree.(fs.parent)->subtree➅➀
	➀➅changedFS[fs, fs'] ➅➀
}

run rm with exactly ➀,➅ for 4 but 2 AMap, 4 Inode
run rmdir with exactly ➀,➅ for 4 but 2 AMap, 4 Inode
run rm_r with exactly ➀,➅for 4 but 2 AMap, 4 Inode

// rm removes exactly the specified file
assert rmRemovesOneFile {
 ➀➅ all fs, fs': AMap, f: File |
    rm[fs, fs', f]=> fs.objects - f = fs'.objects➅➀
}

// rmdir removes exactly the specified directory
assert rmdirRemovesOneDir {
 ➀➅ all fs, fs': AMap, d: Dir |
    rmdir[fs, fs', d] => fs.objects - d = fs'.objects➅➀
}

// rm_r removes exactly the specified subtree
assert rm_rRemovesSubtree {
  ➀➅all fs, fs': AMap, f: Inode |
    rm_r[fs, fs', f] => fs.objects - f.*(fs.contents) = fs'.objects➅➀
}

// rm and rm_r same effect on files
assert rmAndrm_rSameForFiles {
  ➀➅all fs, fs1, fs2: AMap, f: File |
    rm[fs, fs1, f] && rm_r[fs, fs2, f] => fs1.contents = fs2.contents➅➀
}

// removal operations don't change another existing filesystem
assert rmKeepsDisjointFilesystemsUnchanged {
	➀➅all fs, fs', fs2: AMap, f: File |
		rm[fs, fs', f] && disjointPartitions[fs, fs2]
		=> changedFS[fs, fs'] && disjointPartitions[fs', fs2]➅➀
}
assert rmdirKeepsDisjointFilesystemsUnchanged {
	➀➅all fs, fs', fs2: AMap, d: Dir |
		rmdir[fs, fs', d] && disjointPartitions[fs, fs2]
		=> changedFS[fs, fs'] && disjointPartitions[fs', fs2]➅➀
}
assert rm_rKeepsDisjointFilesystemsUnchanged {
	➀➅all fs, fs', fs2: AMap, n: Inode |
		rm_r[fs, fs', n] && disjointPartitions[fs, fs2]
		=> changedFS[fs, fs'] && disjointPartitions[fs', fs2]➅➀
}

check rmRemovesOneFile  with exactly ➀,➅ for 5   
check rmdirRemovesOneDir  with exactly ➀,➅ for 5    
check rm_rRemovesSubtree  with exactly ➀,➅for 5    
check rmAndrm_rSameForFiles  with exactly ➀,➅for 5 
check rmKeepsDisjointFilesystemsUnchanged with exactly ➀,➅ for 5 
check rmdirKeepsDisjointFilesystemsUnchanged with exactly ➀,➅ for 5 
check rm_rKeepsDisjointFilesystemsUnchanged with exactly ➀,➅ for 5 


// rm frees memory (in this model, every file uses at least one block)
assert rmFreesMemory {
  ➀➁➅all fs, fs': AMap, f: File |
    rm[fs, fs', f]=> df[fs'] > df[fs]➅➁➀
}

// rmdir (inside a FS) does not change the storage state of the filesystem
assert rmdirKeepsStorageStateUnchanged {
  ➀➁➅all fs, fs': AMap, dir: Dir |
    rmdir[fs, fs', dir]=> fs.datablocks = fs'.datablocks➅➁➀
}

// rm_r frees memory (in this model, every file uses at least one block)
assert rm_rFreesMemory {
  ➀➁➅all fs, fs': AMap, n: Inode |
    rm_r[fs, fs', n] && some File&n.^(fs.contents) => df[fs'] > df[fs]➅➁➀
}

check rmFreesMemory with exactly ➀,➁,➅ for 5   
check rmdirKeepsStorageStateUnchanged with exactly ➀,➁,➅ for 5 
check rm_rFreesMemory with exactly ➀,➁,➅ for 5   


// Symbolic links may point to one target. This target may not be a Symlink itself.
fact SymLinks_fact {
	// may contain invalid target in order to comply with delete and move operations
	➆➀all m: AMap, l: SymLink | l in m.objects => (#l.(m.contents) <2) && l.(m.contents) in (Inode-SymLink)➀➆
	//all m: AMap | ((m.objects&SymLink) -> (SymLink.(m.symlinks))) = m.symlinks
}


// These links are actually hard- and symlinks
// - hard links: they point directly to Inodes (there is no notion of path names)
// - sym links: they are Inodes themselves, cross fs boundaries (limited) and may be broken
➀➆sig SymLink extends Composite { } ➆➀

// This predicate only works for two AMap-Filesystems (thus it is somewhat restricted)
pred symLinksAcrossPartitions[disj fs1,fs2: AMap, link: ➀➆SymLink➆➀] {	
	➆➀disjointPartitions[fs1, fs2]➀➆
	➆➀link in fs1.objects➀➆
	➆➀#(link.(fs1.contents)) > 0➀➆
	➆➀link.(fs1.contents) in fs2.objects➀➆
}

run symLinksAcrossPartitions with exactly ➆,➀ for 4 but 2 AMap, 8 Inode


// recursive directory listing following symbolic links, inifinite loop aware (as Alloy naturally is)
fun ls_rH[cd: ➀Dir➀] : set ➀Inode➀ {
	➆➃➀cd.^(AMap.contents)➀➃➆
}

// there is an Inode in a different file system reachable with ls_rH
pred ls_rH_crossesFSboundaries {
	➆➃➀some fs1, fs2: AMap, cd:Dir, n: Inode |
		cd in fs1.objects &&
		n in ls_rH[cd] &&
		disjointPartitions[fs1, fs2] &&
		n in fs2.objects➀➃➆
}

run ls_rH_crossesFSboundaries with exactly ➀,➃,➆ for 5




