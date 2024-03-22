// See LICENSE for license details.

#include "cachesim.h"
#include "common.h"
#include <cstdlib>
#include <iostream>
#include <iomanip>

cache_sim_t::cache_sim_t(size_t _sets, size_t _ways, size_t _linesz, const char* _name)
: sets(_sets), ways(_ways), linesz(_linesz), name(_name), log(false)
{
  init();
}

static void help()
{
  std::cerr << "Cache configurations must be of the form" << std::endl;
  std::cerr << "  sets:ways:blocksize" << std::endl;
  std::cerr << "where sets, ways, and blocksize are positive integers, with" << std::endl;
  std::cerr << "sets and blocksize both powers of two and blocksize at least 8." << std::endl;
  exit(1);
}
char* policy = new char[2];
/*
 * Added char policy to store the policy,
 * and updated the string tokenize part to also store the options.
 */
cache_sim_t* cache_sim_t::construct(const char* config, const char* name)
{
  const char* wp = strchr(config, ':');
  if (!wp++) help();
  const char* bp = strchr(wp, ':');
  if (!bp++) help();
  const char* cp = strchr(bp, ':');
  size_t sets = atoi(std::string(config, wp).c_str());
  size_t ways = atoi(std::string(wp, bp).c_str());
  size_t linesz = atoi(std::string(bp,cp).c_str());
  policy[0] = cp[1];
  policy[1] = '\0'; 
  if (ways > 4 /* empirical */ && sets == 1)
    return new fa_cache_sim_t(ways, linesz, name);
  return new cache_sim_t(sets, ways, linesz, name);
}
/*
 * Added LRUCount, FIFOCount, LRUTime, FIFOTime.
 * LRUCount, FIFOCount is counters for each LRU - FIFO Case,
 * LRUTime / FIFOTime is the storage for LRU and FIFO Case,
 * to determine how old is the item in cache.
 */
void cache_sim_t::init()
{
  if(sets == 0 || (sets & (sets-1)))
    help();
  if(linesz < 8 || (linesz & (linesz-1)))
    help();

  idx_shift = 0;
  for (size_t x = linesz; x>1; x >>= 1)
    idx_shift++;

  LRUCount = 0;
  FIFOCount = 0;
  LRUTime = new int[sets*ways]();
  FIFOTime = new int[sets*ways]();

  tags = new uint64_t[sets*ways]();
  read_accesses = 0;
  read_misses = 0;
  bytes_read = 0;
  write_accesses = 0;
  write_misses = 0;
  bytes_written = 0;
  writebacks = 0;

  miss_handler = NULL;
}

cache_sim_t::cache_sim_t(const cache_sim_t& rhs)
 : sets(rhs.sets), ways(rhs.ways), linesz(rhs.linesz),
   idx_shift(rhs.idx_shift), name(rhs.name), log(false)
{
  tags = new uint64_t[sets*ways];
  memcpy(tags, rhs.tags, sets*ways*sizeof(uint64_t));
}

cache_sim_t::~cache_sim_t()
{
  print_stats();
  delete [] tags;
}

void cache_sim_t::print_stats()
{
  if(read_accesses + write_accesses == 0)
    return;

  float mr = 100.0f*(read_misses+write_misses)/(read_accesses+write_accesses);

  std::cout << std::setprecision(3) << std::fixed;
  std::cout << name << " ";
  std::cout << "Bytes Read:            " << bytes_read << std::endl;
  std::cout << name << " ";
  std::cout << "Bytes Written:         " << bytes_written << std::endl;
  std::cout << name << " ";
  std::cout << "Read Accesses:         " << read_accesses << std::endl;
  std::cout << name << " ";
  std::cout << "Write Accesses:        " << write_accesses << std::endl;
  std::cout << name << " ";
  std::cout << "Read Misses:           " << read_misses << std::endl;
  std::cout << name << " ";
  std::cout << "Write Misses:          " << write_misses << std::endl;
  std::cout << name << " ";
  std::cout << "Writebacks:            " << writebacks << std::endl;
  std::cout << name << " ";
  std::cout << "Miss Rate:             " << mr << '%' << std::endl;
}
/*
 * All addresses go through check_tag.
 * So, if the address is HIT, I updated the LRU array to make sure that
 * 'This one is the newest'
 * in case of FIFO, we don't update on HIT case, since we only check when it is 'first added' to the cache.
 */
uint64_t* cache_sim_t::check_tag(uint64_t addr)
{
  size_t idx = (addr >> idx_shift) & (sets-1);
  size_t tag = (addr >> idx_shift) | VALID;

  for (size_t i = 0; i < ways; i++)
    if (tag == (tags[idx*ways + i] & ~DIRTY)) {
      if (!strcmp(policy, "L")) LRUTime[idx*ways+i] = LRUCount;
      return &tags[idx*ways + i];
    } 
  return NULL;
}

uint64_t cache_sim_t::victimize(uint64_t addr)
{
  size_t idx = (addr >> idx_shift) & (sets-1);
  size_t way = lfsr.next() % ways;
  uint64_t victim = tags[idx*ways + way];
  tags[idx*ways + way] = (addr >> idx_shift) | VALID;
  return victim;
}

/* Custom function LRU*/
/*
 * for LRU, we need to keep the [history] of each caches. let's use counter.
 * for ex, if they accessed way[9] way[10] way[8] way[4] way[5], give each of them counters 1,2,3,4,5
 * when finding victim to eliminate, check the counters and the least countered one is the oldest.
 * To store which is the oldest one, I used LRUTime[tags*sets] to store the counters.
 *
 */
uint64_t cache_sim_t::LRU(uint64_t addr)
{
  size_t idx = (addr >> idx_shift) & (sets-1);
  size_t way = 0;
  int count = 2147483647;
  bool isSthEmpty = false;
  for (size_t i = 0 ; i < ways ; i++) {
	  if (tags[idx*ways + i] == 0) {
		  LRUTime[idx*ways+i] = LRUCount++;
		  way = i;
		  isSthEmpty = true;
		  break;
	  }
  }
  /*
   * First check if there's an empty space in my selected set of cache.
   * If some place is empty, fill inside(set it as victim), update LRUTime, and break.
   */
  if (!isSthEmpty) {
  	for (size_t i = 0 ; i < ways ; i++) {
		  if (LRUTime[idx*ways + i] < count) {
			  count = LRUTime[idx*ways + i];
			  way = i;
		  }
	}
  }
  /*
   * If my selected set is full, check the smallest-LRUTime valued line in my set.
   * That set is the least-recently-used one, so eliminate it. (Set it as victim)
   */
  uint64_t victim = tags[idx*ways + way];
  LRUTime[idx*ways+way] = LRUCount++;
  tags[idx*ways + way] = (addr >> idx_shift) | VALID;
  return victim;
}
/*
 * CUSTOM FUNCTION FIFO
 * FIFO works same as LRU, only with different storage and different counter.
 * First check if the location on tag is empty,
 * if its empty, fill the tag,
 * if it is not, check the FIFOTime array to eliminate the most outdated one.
 * And then update the time to newest on that location.
 */
uint64_t cache_sim_t::FIFO(uint64_t addr)
{
  size_t idx = (addr >> idx_shift) & (sets-1);
  size_t way = 0;
  int count = 2147483647;
  bool isSthEmpty = false;
  for (size_t i = 0 ; i < ways ; i++) {
	  if (tags[idx*ways + i] == 0) {
		  FIFOTime[idx*ways+i] = FIFOCount;
		  way = i;
		  isSthEmpty = true;
		  break;
	  }
  }
  if (!isSthEmpty) {
	  for (size_t i = 0 ; i < ways ; i++) {
		  if (FIFOTime[idx*ways + i] < count) {
			  count = FIFOTime[idx*ways + i];
			  way = i;
		  }
	  }
  }
  uint64_t victim = tags[idx*ways + way];
  FIFOTime[idx*ways+way] = FIFOCount;
  tags[idx*ways + way] = (addr >> idx_shift) | VALID;
  return victim;
}
/*
 * ACCESS
 * only added some cases to check if the policy is L, F, or R.
 * Nothing else is modified except those ones.
 * In case of counters, LRUCount and FIFOCount are incremented each time access is called,
 * since every memory-address calls invoke cache_sim_t::access,
 * LRUCount and FIFOCount in this case can be a good indicator for how long the cache has been inside
 * since the last update.
 *
 * For example, in LRUTime[], if LRUTime[11] = 45, it means cache data in tags[11] is most recently accessed
 * when 45th address is interpreted at cache_sim_t::access,
 * in FIFOTime[], if FIFOTime[12] = 32, it means cache data in tags[12] is recently updated
 * when 32th address is interpreted at cache_sim_t::access.
 */
void cache_sim_t::access(uint64_t addr, size_t bytes, bool store)
{
  if (!strcmp(policy, "L")) LRUCount++;
  if (!strcmp(policy, "F")) FIFOCount++;

  store ? write_accesses++ : read_accesses++;
  (store ? bytes_written : bytes_read) += bytes;

  uint64_t* hit_way = check_tag(addr);
  if (likely(hit_way != NULL))
  {
    if (store)
      *hit_way |= DIRTY;
    return;
  }

  store ? write_misses++ : read_misses++;
  if (log)
  {
    std::cerr << name << " "
              << (store ? "write" : "read") << " miss 0x"
              << std::hex << addr << std::endl;
  }

  uint64_t victim = 0;
  if (!strcmp(policy, "R")) victim = victimize(addr);
  else if (!strcmp(policy, "L")) victim = LRU(addr);
  else if (!strcmp(policy, "F")) victim = FIFO(addr);

  if ((victim & (VALID | DIRTY)) == (VALID | DIRTY))
  {
    uint64_t dirty_addr = (victim & ~(VALID | DIRTY)) << idx_shift;
    if (miss_handler)
      miss_handler->access(dirty_addr, linesz, true);
    writebacks++;
  }

  if (miss_handler)
    miss_handler->access(addr & ~(linesz-1), linesz, false);

  if (store)
    *check_tag(addr) |= DIRTY;
}

fa_cache_sim_t::fa_cache_sim_t(size_t ways, size_t linesz, const char* name)
  : cache_sim_t(1, ways, linesz, name)
{
}

uint64_t* fa_cache_sim_t::check_tag(uint64_t addr)
{
  auto it = tags.find(addr >> idx_shift);
  return it == tags.end() ? NULL : &it->second;
}

uint64_t fa_cache_sim_t::victimize(uint64_t addr)
{
  uint64_t old_tag = 0;
  if (tags.size() == ways)
  {
    auto it = tags.begin();
    std::advance(it, lfsr.next() % ways);
    old_tag = it->second;
    tags.erase(it);
  }
  tags[addr >> idx_shift] = (addr >> idx_shift) | VALID;
  return old_tag;
}
