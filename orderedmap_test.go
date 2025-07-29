package orderedmap

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestBasicFeatures(t *testing.T) {
	n := 100
	om := New[int, int]()

	// set(i, 2 * i)
	for i := 0; i < n; i++ {
		assertLenEqual(t, om, i)
		oldValue, present := om.Set(i, 2*i)
		assertLenEqual(t, om, i+1)

		assert.Equal(t, 0, oldValue)
		assert.False(t, present)
	}

	// get what we just set
	for i := 0; i < n; i++ {
		value, present := om.Get(i)

		assert.Equal(t, 2*i, value)
		assert.Equal(t, value, om.Value(i))
		assert.True(t, present)
	}

	// get pairs of what we just set
	for i := 0; i < n; i++ {
		pair := om.GetPair(i)

		assert.NotNil(t, pair)
		assert.Equal(t, 2*i, pair.Value)
	}

	// forward iteration
	i := 0
	for pair := om.Oldest(); pair != nil; pair = pair.Next() {
		assert.Equal(t, i, pair.Key)
		assert.Equal(t, 2*i, pair.Value)
		i++
	}
	// backward iteration
	i = n - 1
	for pair := om.Newest(); pair != nil; pair = pair.Prev() {
		assert.Equal(t, i, pair.Key)
		assert.Equal(t, 2*i, pair.Value)
		i--
	}

	// forward iteration starting from known key
	i = 42
	for pair := om.GetPair(i); pair != nil; pair = pair.Next() {
		assert.Equal(t, i, pair.Key)
		assert.Equal(t, 2*i, pair.Value)
		i++
	}

	// double values for pairs with even keys
	for j := 0; j < n/2; j++ {
		i = 2 * j
		oldValue, present := om.Set(i, 4*i)

		assert.Equal(t, 2*i, oldValue)
		assert.True(t, present)
	}
	// and delete pairs with odd keys
	for j := 0; j < n/2; j++ {
		i = 2*j + 1
		assertLenEqual(t, om, n-j)
		value, present := om.Delete(i)
		assertLenEqual(t, om, n-j-1)

		assert.Equal(t, 2*i, value)
		assert.True(t, present)

		// deleting again shouldn't change anything
		value, present = om.Delete(i)
		assertLenEqual(t, om, n-j-1)
		assert.Equal(t, 0, value)
		assert.False(t, present)
	}

	// get the whole range
	for j := 0; j < n/2; j++ {
		i = 2 * j
		value, present := om.Get(i)
		assert.Equal(t, 4*i, value)
		assert.Equal(t, value, om.Value(i))
		assert.True(t, present)

		i = 2*j + 1
		value, present = om.Get(i)
		assert.Equal(t, 0, value)
		assert.Equal(t, value, om.Value(i))
		assert.False(t, present)
	}

	// check iterations again
	i = 0
	for pair := om.Oldest(); pair != nil; pair = pair.Next() {
		assert.Equal(t, i, pair.Key)
		assert.Equal(t, 4*i, pair.Value)
		i += 2
	}
	i = 2 * ((n - 1) / 2)
	for pair := om.Newest(); pair != nil; pair = pair.Prev() {
		assert.Equal(t, i, pair.Key)
		assert.Equal(t, 4*i, pair.Value)
		i -= 2
	}
}

func TestUpdatingDoesntChangePairsOrder(t *testing.T) {
	om := New[string, any]()
	om.Set("foo", "bar")
	om.Set("wk", 28)
	om.Set("po", 100)
	om.Set("bar", "baz")

	oldValue, present := om.Set("po", 102)
	assert.Equal(t, 100, oldValue)
	assert.True(t, present)

	assertOrderedPairsEqual(t, om,
		[]string{"foo", "wk", "po", "bar"},
		[]any{"bar", 28, 102, "baz"})
}

func TestDeletingAndReinsertingChangesPairsOrder(t *testing.T) {
	om := New[string, any]()
	om.Set("foo", "bar")
	om.Set("wk", 28)
	om.Set("po", 100)
	om.Set("bar", "baz")

	// delete a pair
	oldValue, present := om.Delete("po")
	assert.Equal(t, 100, oldValue)
	assert.True(t, present)

	// re-insert the same pair
	oldValue, present = om.Set("po", 100)
	assert.Nil(t, oldValue)
	assert.False(t, present)

	assertOrderedPairsEqual(t, om,
		[]string{"foo", "wk", "bar", "po"},
		[]any{"bar", 28, "baz", 100})
}

func TestEmptyMapOperations(t *testing.T) {
	om := New[string, any]()

	oldValue, present := om.Get("foo")
	assert.Nil(t, oldValue)
	assert.Nil(t, om.Value("foo"))
	assert.False(t, present)

	oldValue, present = om.Delete("bar")
	assert.Nil(t, oldValue)
	assert.False(t, present)

	assertLenEqual(t, om, 0)

	assert.Nil(t, om.Oldest())
	assert.Nil(t, om.Newest())
}

type dummyTestStruct struct {
	value string
}

func TestPackUnpackStructs(t *testing.T) {
	om := New[string, dummyTestStruct]()
	om.Set("foo", dummyTestStruct{"foo!"})
	om.Set("bar", dummyTestStruct{"bar!"})

	value, present := om.Get("foo")
	assert.True(t, present)
	assert.Equal(t, value, om.Value("foo"))
	if assert.NotNil(t, value) {
		assert.Equal(t, "foo!", value.value)
	}

	value, present = om.Set("bar", dummyTestStruct{"baz!"})
	assert.True(t, present)
	if assert.NotNil(t, value) {
		assert.Equal(t, "bar!", value.value)
	}

	value, present = om.Get("bar")
	assert.Equal(t, value, om.Value("bar"))
	assert.True(t, present)
	if assert.NotNil(t, value) {
		assert.Equal(t, "baz!", value.value)
	}
}

// shamelessly stolen from https://github.com/python/cpython/blob/e19a91e45fd54a56e39c2d12e6aaf4757030507f/Lib/test/test_ordered_dict.py#L55-L61
func TestShuffle(t *testing.T) {
	ranLen := 100

	for _, n := range []int{0, 10, 20, 100, 1000, 10000} {
		t.Run(fmt.Sprintf("shuffle test with %d items", n), func(t *testing.T) {
			om := New[string, string]()

			keys := make([]string, n)
			values := make([]string, n)

			for i := 0; i < n; i++ {
				// we prefix with the number to ensure that we don't get any duplicates
				keys[i] = fmt.Sprintf("%d_%s", i, randomHexString(t, ranLen))
				values[i] = randomHexString(t, ranLen)

				value, present := om.Set(keys[i], values[i])
				assert.Equal(t, "", value)
				assert.False(t, present)
			}

			assertOrderedPairsEqual(t, om, keys, values)
		})
	}
}

func TestMove(t *testing.T) {
	om := New[int, any]()
	om.Set(1, "bar")
	om.Set(2, 28)
	om.Set(3, 100)
	om.Set(4, "baz")
	om.Set(5, "28")
	om.Set(6, "100")
	om.Set(7, "baz")
	om.Set(8, "baz")

	err := om.MoveAfter(2, 3)
	assert.Nil(t, err)
	assertOrderedPairsEqual(t, om,
		[]int{1, 3, 2, 4, 5, 6, 7, 8},
		[]any{"bar", 100, 28, "baz", "28", "100", "baz", "baz"})

	err = om.MoveBefore(6, 4)
	assert.Nil(t, err)
	assertOrderedPairsEqual(t, om,
		[]int{1, 3, 2, 6, 4, 5, 7, 8},
		[]any{"bar", 100, 28, "100", "baz", "28", "baz", "baz"})

	err = om.MoveToBack(3)
	assert.Nil(t, err)
	assertOrderedPairsEqual(t, om,
		[]int{1, 2, 6, 4, 5, 7, 8, 3},
		[]any{"bar", 28, "100", "baz", "28", "baz", "baz", 100})

	err = om.MoveToFront(5)
	assert.Nil(t, err)
	assertOrderedPairsEqual(t, om,
		[]int{5, 1, 2, 6, 4, 7, 8, 3},
		[]any{"28", "bar", 28, "100", "baz", "baz", "baz", 100})

	err = om.MoveToFront(100)
	assert.Equal(t, &KeyNotFoundError[int]{100}, err)
}

func TestGetAndMove(t *testing.T) {
	om := New[int, any]()
	om.Set(1, "bar")
	om.Set(2, 28)
	om.Set(3, 100)
	om.Set(4, "baz")
	om.Set(5, "28")
	om.Set(6, "100")
	om.Set(7, "baz")
	om.Set(8, "baz")

	value, err := om.GetAndMoveToBack(3)
	assert.Nil(t, err)
	assert.Equal(t, 100, value)
	assertOrderedPairsEqual(t, om,
		[]int{1, 2, 4, 5, 6, 7, 8, 3},
		[]any{"bar", 28, "baz", "28", "100", "baz", "baz", 100})

	value, err = om.GetAndMoveToFront(5)
	assert.Nil(t, err)
	assert.Equal(t, "28", value)
	assertOrderedPairsEqual(t, om,
		[]int{5, 1, 2, 4, 6, 7, 8, 3},
		[]any{"28", "bar", 28, "baz", "100", "baz", "baz", 100})

	value, err = om.GetAndMoveToBack(100)
	assert.Equal(t, &KeyNotFoundError[int]{100}, err)
}

func TestAddPairs(t *testing.T) {
	om := New[int, any]()
	om.AddPairs(
		Pair[int, any]{
			Key:   28,
			Value: "foo",
		},
		Pair[int, any]{
			Key:   12,
			Value: "bar",
		},
		Pair[int, any]{
			Key:   28,
			Value: "baz",
		},
	)

	assertOrderedPairsEqual(t, om,
		[]int{28, 12},
		[]any{"baz", "bar"})
}

// sadly, we can't test the "actual" capacity here, see https://github.com/golang/go/issues/52157
func TestNewWithCapacity(t *testing.T) {
	zero := New[int, string](0)
	assert.Empty(t, zero.Len())

	assert.PanicsWithValue(t, invalidOptionMessage, func() {
		_ = New[int, string](1, 2)
	})
	assert.PanicsWithValue(t, invalidOptionMessage, func() {
		_ = New[int, string](1, 2, 3)
	})

	om := New[int, string](-1)
	om.Set(1337, "quarante-deux")
	assert.Equal(t, 1, om.Len())
}

func TestNewWithOptions(t *testing.T) {
	t.Run("wih capacity", func(t *testing.T) {
		om := New[string, any](WithCapacity[string, any](98))
		assert.Equal(t, 0, om.Len())
	})

	t.Run("with initial data", func(t *testing.T) {
		om := New[string, int](WithInitialData(
			Pair[string, int]{
				Key:   "a",
				Value: 1,
			},
			Pair[string, int]{
				Key:   "b",
				Value: 2,
			},
			Pair[string, int]{
				Key:   "c",
				Value: 3,
			},
		))

		assertOrderedPairsEqual(t, om,
			[]string{"a", "b", "c"},
			[]int{1, 2, 3})
	})

	t.Run("with an invalid option type", func(t *testing.T) {
		assert.PanicsWithValue(t, invalidOptionMessage, func() {
			_ = New[int, string]("foo")
		})
	})
}

func TestNilMap(t *testing.T) {
	// we want certain behaviors of a nil ordered map to be the same as they are for standard nil maps
	var om *OrderedMap[int, any]

	t.Run("len", func(t *testing.T) {
		assert.Equal(t, 0, om.Len())
	})

	t.Run("iterating - akin to range", func(t *testing.T) {
		assert.Nil(t, om.Oldest())
		assert.Nil(t, om.Newest())
	})
}

func TestIterators(t *testing.T) {
	om := New[int, any]()
	om.Set(1, "bar")
	om.Set(2, 28)
	om.Set(3, 100)
	om.Set(4, "baz")
	om.Set(5, "28")
	om.Set(6, "100")
	om.Set(7, "baz")
	om.Set(8, "baz")

	expectedKeys := []int{1, 2, 3, 4, 5, 6, 7, 8}
	expectedKeysFromNewest := []int{8, 7, 6, 5, 4, 3, 2, 1}
	expectedValues := []any{"bar", 28, 100, "baz", "28", "100", "baz", "baz"}
	expectedValuesFromNewest := []any{"baz", "baz", "100", "28", "baz", 100, 28, "bar"}

	var keys []int
	var values []any

	for k, v := range om.FromOldest() {
		keys = append(keys, k)
		values = append(values, v)
	}

	assert.Equal(t, expectedKeys, keys)
	assert.Equal(t, expectedValues, values)

	keys, values = []int{}, []any{}

	for k, v := range om.FromNewest() {
		keys = append(keys, k)
		values = append(values, v)
	}

	assert.Equal(t, expectedKeysFromNewest, keys)
	assert.Equal(t, expectedValuesFromNewest, values)

	keys = []int{}

	for k := range om.KeysFromOldest() {
		keys = append(keys, k)
	}

	assert.Equal(t, expectedKeys, keys)

	keys = []int{}

	for k := range om.KeysFromNewest() {
		keys = append(keys, k)
	}

	assert.Equal(t, expectedKeysFromNewest, keys)

	values = []any{}

	for v := range om.ValuesFromOldest() {
		values = append(values, v)
	}

	assert.Equal(t, expectedValues, values)

	values = []any{}

	for v := range om.ValuesFromNewest() {
		values = append(values, v)
	}

	assert.Equal(t, expectedValuesFromNewest, values)
}

func TestIteratorsFrom(t *testing.T) {
	om := New[int, any]()
	om.Set(1, "bar")
	om.Set(2, 28)
	om.Set(3, 100)
	om.Set(4, "baz")
	om.Set(5, "28")
	om.Set(6, "100")
	om.Set(7, "baz")
	om.Set(8, "baz")

	om2 := From(om.FromOldest())

	expectedKeys := []int{1, 2, 3, 4, 5, 6, 7, 8}
	expectedValues := []any{"bar", 28, 100, "baz", "28", "100", "baz", "baz"}

	var keys []int
	var values []any

	for k, v := range om2.FromOldest() {
		keys = append(keys, k)
		values = append(values, v)
	}

	assert.Equal(t, expectedKeys, keys)
	assert.Equal(t, expectedValues, values)

	expectedKeysFromNewest := []int{8, 7, 6, 5, 4, 3, 2, 1}
	expectedValuesFromNewest := []any{"baz", "baz", "100", "28", "baz", 100, 28, "bar"}

	om2 = From(om.FromNewest())

	keys = []int{}
	values = []any{}

	for k, v := range om2.FromOldest() {
		keys = append(keys, k)
		values = append(values, v)
	}

	assert.Equal(t, expectedKeysFromNewest, keys)
	assert.Equal(t, expectedValuesFromNewest, values)
}

func TestFilter(t *testing.T) {
	om := New[int, int]()

	n := 10 * 3 // ensure divisibility by 3 for the length check below
	for i := range n {
		om.Set(i, i*i)
	}

	om.Filter(func(k, v int) bool {
		return k%3 == 0
	})

	assert.Equal(t, n/3, om.Len())
	for k := range om.FromOldest() {
		assert.True(t, k%3 == 0)
	}
}

func TestInsertAfter(t *testing.T) {
	t.Run("insert after existing key", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")

		om.InsertAfter(2, 5, "five")

		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 5, 3},
			[]string{"one", "two", "five", "three"})
	})

	t.Run("insert after first key", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")

		om.InsertAfter(1, 3, "three")

		assertOrderedPairsEqual(t, om,
			[]int{1, 3, 2},
			[]string{"one", "three", "two"})
	})

	t.Run("insert after last key", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")

		om.InsertAfter(2, 3, "three")

		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 3},
			[]string{"one", "two", "three"})
	})

	t.Run("insert after non-existent key acts as Set", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")

		om.InsertAfter(99, 3, "three")

		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 3},
			[]string{"one", "two", "three"})
	})

	t.Run("insert after non-existent key in empty map", func(t *testing.T) {
		om := New[int, string]()

		om.InsertAfter(99, 1, "one")

		assertOrderedPairsEqual(t, om,
			[]int{1},
			[]string{"one"})
	})

	t.Run("insert existing key after another key", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")

		om.InsertAfter(2, 1, "one_updated")

		assertOrderedPairsEqual(t, om,
			[]int{2, 1, 3},
			[]string{"two", "one_updated", "three"})
	})
}

func TestInsertBefore(t *testing.T) {
	t.Run("insert before existing key", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")

		om.InsertBefore(3, 5, "five")

		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 5, 3},
			[]string{"one", "two", "five", "three"})
	})

	t.Run("insert before first key", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")

		om.InsertBefore(1, 3, "three")

		assertOrderedPairsEqual(t, om,
			[]int{3, 1, 2},
			[]string{"three", "one", "two"})
	})

	t.Run("insert before last key", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")

		om.InsertBefore(2, 3, "three")

		assertOrderedPairsEqual(t, om,
			[]int{1, 3, 2},
			[]string{"one", "three", "two"})
	})

	t.Run("insert before non-existent key acts as Set", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")

		om.InsertBefore(99, 3, "three")

		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 3},
			[]string{"one", "two", "three"})
	})

	t.Run("insert before non-existent key in empty map", func(t *testing.T) {
		om := New[int, string]()

		om.InsertBefore(99, 1, "one")

		assertOrderedPairsEqual(t, om,
			[]int{1},
			[]string{"one"})
	})

	t.Run("insert existing key before another key", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")

		om.InsertBefore(2, 3, "three_updated")

		assertOrderedPairsEqual(t, om,
			[]int{1, 3, 2},
			[]string{"one", "three_updated", "two"})
	})
}

func TestReplace(t *testing.T) {
	t.Run("replace existing key with new key", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")

		om.Replace(2, 5, "five")

		assertOrderedPairsEqual(t, om,
			[]int{1, 5, 3},
			[]string{"one", "five", "three"})
	})

	t.Run("replace first key", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")

		om.Replace(1, 3, "three")

		assertOrderedPairsEqual(t, om,
			[]int{3, 2},
			[]string{"three", "two"})
	})

	t.Run("replace last key", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")

		om.Replace(2, 3, "three")

		assertOrderedPairsEqual(t, om,
			[]int{1, 3},
			[]string{"one", "three"})
	})

	t.Run("replace with existing key", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")

		om.Replace(2, 3, "three_updated")

		assertOrderedPairsEqual(t, om,
			[]int{1, 3},
			[]string{"one", "three_updated"})
	})

	t.Run("replace non-existent key acts as Set", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")

		om.Replace(99, 3, "three")

		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 3},
			[]string{"one", "two", "three"})
	})

	t.Run("replace non-existent key in empty map", func(t *testing.T) {
		om := New[int, string]()

		om.Replace(99, 1, "one")

		assertOrderedPairsEqual(t, om,
			[]int{1},
			[]string{"one"})
	})

	t.Run("replace with same key but different value", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")

		om.Replace(2, 2, "two_updated")

		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 3},
			[]string{"one", "two_updated", "three"})
	})

	t.Run("replace in single element map", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")

		om.Replace(1, 2, "two")

		assertOrderedPairsEqual(t, om,
			[]int{2},
			[]string{"two"})
	})
}

func TestReplaceWhileIterating(t *testing.T) {
	t.Run("replace during FromOldest iteration", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")
		om.Set(4, "four")
		om.Set(5, "five")

		var visitedKeys []int
		var visitedValues []string

		for k, v := range om.FromOldest() {
			visitedKeys = append(visitedKeys, k)
			visitedValues = append(visitedValues, v)

			// Replace the middle element during iteration
			if k == 3 {
				om.Replace(3, 6, "six")
			}
		}

		// Should visit all elements - the replaced element shows original key/value during iteration
		// because the iterator captured it before the replacement
		expectedKeys := []int{1, 2, 3, 4, 5}
		expectedValues := []string{"one", "two", "three", "four", "five"}

		assert.Equal(t, expectedKeys, visitedKeys, "iteration should visit all elements without breaking")
		assert.Equal(t, expectedValues, visitedValues, "iteration should show captured values at yield time")

		// Verify final state of the map shows the replacement
		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 6, 4, 5},
			[]string{"one", "two", "six", "four", "five"})
	})

	t.Run("replace during FromNewest iteration", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")
		om.Set(4, "four")
		om.Set(5, "five")

		var visitedKeys []int
		var visitedValues []string

		for k, v := range om.FromNewest() {
			visitedKeys = append(visitedKeys, k)
			visitedValues = append(visitedValues, v)

			// Replace the middle element during iteration
			if k == 3 {
				om.Replace(3, 7, "seven")
			}
		}

		// Should visit all elements in reverse order, showing original values during iteration
		expectedKeys := []int{5, 4, 3, 2, 1}
		expectedValues := []string{"five", "four", "three", "two", "one"}

		assert.Equal(t, expectedKeys, visitedKeys, "iteration should visit all elements without breaking")
		assert.Equal(t, expectedValues, visitedValues, "iteration should show captured values at yield time")

		// Verify final state of the map shows the replacement
		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 7, 4, 5},
			[]string{"one", "two", "seven", "four", "five"})
	})

	t.Run("replace first element during FromOldest iteration", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")

		var visitedKeys []int
		var visitedValues []string

		for k, v := range om.FromOldest() {
			visitedKeys = append(visitedKeys, k)
			visitedValues = append(visitedValues, v)

			// Replace the first element during iteration
			if k == 1 {
				om.Replace(1, 10, "ten")
			}
		}

		// Should visit all elements, showing original first element during iteration
		expectedKeys := []int{1, 2, 3}
		expectedValues := []string{"one", "two", "three"}

		assert.Equal(t, expectedKeys, visitedKeys, "iteration should visit all elements without breaking")
		assert.Equal(t, expectedValues, visitedValues, "iteration should show captured values at yield time")

		// Verify final state shows the replacement
		assertOrderedPairsEqual(t, om,
			[]int{10, 2, 3},
			[]string{"ten", "two", "three"})
	})

	t.Run("replace last element during FromNewest iteration", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")

		var visitedKeys []int
		var visitedValues []string

		for k, v := range om.FromNewest() {
			visitedKeys = append(visitedKeys, k)
			visitedValues = append(visitedValues, v)

			// Replace the last element (first in newest iteration) during iteration
			if k == 3 {
				om.Replace(3, 30, "thirty")
			}
		}

		// Should visit all elements, showing original last element during iteration
		expectedKeys := []int{3, 2, 1}
		expectedValues := []string{"three", "two", "one"}

		assert.Equal(t, expectedKeys, visitedKeys, "iteration should visit all elements without breaking")
		assert.Equal(t, expectedValues, visitedValues, "iteration should show captured values at yield time")

		// Verify final state shows the replacement
		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 30},
			[]string{"one", "two", "thirty"})
	})

	t.Run("replace with existing key during iteration", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")
		om.Set(4, "four")
		om.Set(5, "five")

		var visitedKeys []int
		var visitedValues []string

		for k, v := range om.FromOldest() {
			visitedKeys = append(visitedKeys, k)
			visitedValues = append(visitedValues, v)

			// Replace element 2 with key 4 (which already exists) - should remove original 4
			if k == 2 {
				om.Replace(2, 4, "new_four")
			}
		}

		// Should visit all original elements during iteration (captured at yield time)
		// The key 4 should only appear once since original element 4 gets removed
		expectedKeys := []int{1, 2, 3, 5}
		expectedValues := []string{"one", "two", "three", "five"}

		assert.Equal(t, expectedKeys, visitedKeys, "iteration should visit all elements without skipping")
		assert.Equal(t, expectedValues, visitedValues, "iteration should show captured values at yield time")

		// Final state should have the replaced element in position of original key 2, and original key 4 removed
		assertOrderedPairsEqual(t, om,
			[]int{1, 4, 3, 5},
			[]string{"one", "new_four", "three", "five"})
	})

	t.Run("multiple replacements during iteration", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")
		om.Set(4, "four")
		om.Set(5, "five")

		var visitedKeys []int
		var visitedValues []string

		for k, v := range om.FromOldest() {
			visitedKeys = append(visitedKeys, k)
			visitedValues = append(visitedValues, v)

			// Replace multiple elements during iteration
			if k == 2 {
				om.Replace(2, 20, "twenty")
			}
			if k == 4 {
				om.Replace(4, 40, "forty")
			}
		}

		// Should visit all original elements during iteration
		expectedKeys := []int{1, 2, 3, 4, 5}
		expectedValues := []string{"one", "two", "three", "four", "five"}

		assert.Equal(t, expectedKeys, visitedKeys, "iteration should visit all elements without breaking")
		assert.Equal(t, expectedValues, visitedValues, "iteration should show captured values at yield time")

		// Final state should show both replacements
		assertOrderedPairsEqual(t, om,
			[]int{1, 20, 3, 40, 5},
			[]string{"one", "twenty", "three", "forty", "five"})
	})

	t.Run("iteration continues after replacement doesn't break linked list", func(t *testing.T) {
		// This is the most important test - ensuring the linked list structure remains intact
		om := New[int, string]()
		for i := 1; i <= 10; i++ {
			om.Set(i, fmt.Sprintf("value_%d", i))
		}

		visitedCount := 0
		for k, v := range om.FromOldest() {
			visitedCount++
			// Replace every other element during iteration
			if k%2 == 0 {
				om.Replace(k, k+100, fmt.Sprintf("replaced_%d", k+100))
			}
			// Verify we can still access the element
			assert.Equal(t, fmt.Sprintf("value_%d", k), v, "should see original value during iteration")
		}

		// Should visit all 10 elements despite replacements
		assert.Equal(t, 10, visitedCount, "should visit all elements despite replacements")

		// Verify the map still has correct length and structure
		assert.Equal(t, 10, om.Len(), "map should still have 10 elements")

		// Verify we can still iterate through the entire modified map
		finalVisitedCount := 0
		for range om.FromOldest() {
			finalVisitedCount++
		}
		assert.Equal(t, 10, finalVisitedCount, "should be able to iterate through all elements after replacements")
	})
}

func TestInsertWhileIterating(t *testing.T) {
	t.Run("InsertAfter during FromOldest iteration", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")
		om.Set(4, "four")

		var visitedKeys []int
		var visitedValues []string

		for k, v := range om.FromOldest() {
			visitedKeys = append(visitedKeys, k)
			visitedValues = append(visitedValues, v)

			// Insert after element 2 during iteration
			if k == 2 {
				om.InsertAfter(2, 5, "five")
			}
		}

		// Should visit original elements plus the inserted element since it's added after current position
		expectedKeys := []int{1, 2, 5, 3, 4}
		expectedValues := []string{"one", "two", "five", "three", "four"}

		assert.Equal(t, expectedKeys, visitedKeys, "iteration should visit original elements plus inserted element")
		assert.Equal(t, expectedValues, visitedValues, "iteration should include inserted element when positioned ahead")

		// Verify final state shows the insertion
		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 5, 3, 4},
			[]string{"one", "two", "five", "three", "four"})
	})

	t.Run("InsertAfter during FromNewest iteration", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")
		om.Set(4, "four")

		var visitedKeys []int
		var visitedValues []string

		for k, v := range om.FromNewest() {
			visitedKeys = append(visitedKeys, k)
			visitedValues = append(visitedValues, v)

			// Insert after element 3 during iteration
			if k == 3 {
				om.InsertAfter(3, 6, "six")
			}
		}

		// Should visit all original elements in reverse order - inserted element is after element 3
		// but comes before elements 2,1 in reverse iteration, so it won't be visited
		expectedKeys := []int{4, 3, 2, 1}
		expectedValues := []string{"four", "three", "two", "one"}

		assert.Equal(t, expectedKeys, visitedKeys, "iteration should visit original elements without visiting inserted element")
		assert.Equal(t, expectedValues, visitedValues, "iteration should show original values during iteration")

		// Verify final state shows the insertion
		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 3, 6, 4},
			[]string{"one", "two", "three", "six", "four"})
	})

	t.Run("InsertBefore during FromOldest iteration", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")
		om.Set(4, "four")

		var visitedKeys []int
		var visitedValues []string

		for k, v := range om.FromOldest() {
			visitedKeys = append(visitedKeys, k)
			visitedValues = append(visitedValues, v)

			// Insert before element 3 during iteration
			if k == 3 {
				om.InsertBefore(3, 7, "seven")
			}
		}

		// Should visit all original elements - inserted element comes before element 3
		// but is added after we've already passed that position
		expectedKeys := []int{1, 2, 3, 4}
		expectedValues := []string{"one", "two", "three", "four"}

		assert.Equal(t, expectedKeys, visitedKeys, "iteration should visit all original elements")
		assert.Equal(t, expectedValues, visitedValues, "iteration should show original values during iteration")

		// Verify final state shows the insertion
		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 7, 3, 4},
			[]string{"one", "two", "seven", "three", "four"})
	})

	t.Run("InsertBefore during FromNewest iteration", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")
		om.Set(4, "four")

		var visitedKeys []int
		var visitedValues []string

		for k, v := range om.FromNewest() {
			visitedKeys = append(visitedKeys, k)
			visitedValues = append(visitedValues, v)

			// Insert before element 2 during iteration
			if k == 2 {
				om.InsertBefore(2, 8, "eight")
			}
		}

		// Should visit original elements plus the inserted element since it's placed before element 2
		// but after element 1 in the list, so it will be visited before element 1 in reverse iteration
		expectedKeys := []int{4, 3, 2, 8, 1}
		expectedValues := []string{"four", "three", "two", "eight", "one"}

		assert.Equal(t, expectedKeys, visitedKeys, "iteration should visit original elements plus inserted element")
		assert.Equal(t, expectedValues, visitedValues, "iteration should include inserted element when positioned ahead")

		// Verify final state shows the insertion
		assertOrderedPairsEqual(t, om,
			[]int{1, 8, 2, 3, 4},
			[]string{"one", "eight", "two", "three", "four"})
	})

	t.Run("Set new key during FromOldest iteration", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")

		var visitedKeys []int
		var visitedValues []string

		for k, v := range om.FromOldest() {
			visitedKeys = append(visitedKeys, k)
			visitedValues = append(visitedValues, v)

			// Set a new key during iteration - should append to end and be visited
			if k == 2 {
				om.Set(9, "nine")
			}
		}

		// Should visit original elements plus the new element since Set appends to end
		expectedKeys := []int{1, 2, 3, 9}
		expectedValues := []string{"one", "two", "three", "nine"}

		assert.Equal(t, expectedKeys, visitedKeys, "iteration should visit original elements plus new element")
		assert.Equal(t, expectedValues, visitedValues, "iteration should include new element added to end")

		// Verify final state shows the new element at the end
		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 3, 9},
			[]string{"one", "two", "three", "nine"})
	})

	t.Run("insert existing key during iteration", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")
		om.Set(4, "four")
		om.Set(5, "five")

		var visitedKeys []int
		var visitedValues []string

		for k, v := range om.FromOldest() {
			visitedKeys = append(visitedKeys, k)
			visitedValues = append(visitedValues, v)

			// Insert existing key 4 after key 1 (should move key 4)
			if k == 1 {
				om.InsertAfter(1, 4, "four_moved")
			}
		}

		// Should visit element 1, then moved element 4, then remaining elements
		// Key 4 gets moved to position after 1, so it's visited in its new position
		expectedKeys := []int{1, 4, 2, 3, 5}
		expectedValues := []string{"one", "four_moved", "two", "three", "five"}

		assert.Equal(t, expectedKeys, visitedKeys, "iteration should visit moved element in new position")
		assert.Equal(t, expectedValues, visitedValues, "iteration should show updated value for moved element")

		// Verify final state shows the moved element
		assertOrderedPairsEqual(t, om,
			[]int{1, 4, 2, 3, 5},
			[]string{"one", "four_moved", "two", "three", "five"})
	})

	t.Run("multiple insertions during iteration", func(t *testing.T) {
		om := New[int, string]()
		om.Set(1, "one")
		om.Set(2, "two")
		om.Set(3, "three")
		om.Set(4, "four")
		om.Set(5, "five")

		var visitedKeys []int
		var visitedValues []string

		for k, v := range om.FromOldest() {
			visitedKeys = append(visitedKeys, k)
			visitedValues = append(visitedValues, v)

			// Multiple insertions during iteration
			if k == 1 {
				om.InsertAfter(1, 10, "ten")
			}
			if k == 3 {
				om.InsertBefore(3, 30, "thirty")
			}
			if k == 5 {
				om.Set(50, "fifty")
			}
		}

		// Should visit elements including inserted ones that are positioned ahead
		expectedKeys := []int{1, 10, 2, 3, 4, 5, 50}
		expectedValues := []string{"one", "ten", "two", "three", "four", "five", "fifty"}

		assert.Equal(t, expectedKeys, visitedKeys, "iteration should visit original and inserted elements")
		assert.Equal(t, expectedValues, visitedValues, "iteration should show all values including inserted ones")

		// Verify final state shows all insertions
		assertOrderedPairsEqual(t, om,
			[]int{1, 10, 2, 30, 3, 4, 5, 50},
			[]string{"one", "ten", "two", "thirty", "three", "four", "five", "fifty"})
	})

	t.Run("insertions don't break linked list structure", func(t *testing.T) {
		// This is the most important test - ensuring the linked list structure remains intact
		om := New[int, string]()
		for i := 1; i <= 8; i++ {
			om.Set(i, fmt.Sprintf("value_%d", i))
		}

		visitedCount := 0
		insertedElements := make(map[int]bool)

		for k, v := range om.FromOldest() {
			visitedCount++

			// Insert elements at various positions during iteration
			if k == 2 {
				om.InsertAfter(2, 20, "twenty")
				insertedElements[20] = true
			}
			if k == 4 {
				om.InsertBefore(4, 40, "forty")
				insertedElements[40] = true
			}
			if k == 6 {
				om.Set(60, "sixty")
				insertedElements[60] = true
			}
			if k == 8 {
				om.InsertAfter(8, 80, "eighty")
				insertedElements[80] = true
			}

			// Verify we see the expected value - original for original elements, new for inserted elements
			if insertedElements[k] {
				// This is an inserted element, don't check the value format
			} else {
				// This is an original element
				assert.Equal(t, fmt.Sprintf("value_%d", k), v, "should see original value for original element")
			}
		}

		// Should visit more than 8 elements due to insertions that get visited
		assert.Greater(t, visitedCount, 8, "should visit more than original elements due to insertions")

		// Verify the map has the correct final length (8 original + 4 inserted = 12)
		assert.Equal(t, 12, om.Len(), "map should have 12 elements after insertions")

		// Verify we can still iterate through the entire modified map
		finalVisitedCount := 0
		for range om.FromOldest() {
			finalVisitedCount++
		}
		assert.Equal(t, 12, finalVisitedCount, "should be able to iterate through all 12 elements after insertions")

		// Verify we can iterate backwards too
		backwardVisitedCount := 0
		for range om.FromNewest() {
			backwardVisitedCount++
		}
		assert.Equal(t, 12, backwardVisitedCount, "should be able to iterate backwards through all 12 elements")
	})

	t.Run("insert at beginning and end during iteration", func(t *testing.T) {
		om := New[int, string]()
		om.Set(2, "two")
		om.Set(3, "three")
		om.Set(4, "four")

		var visitedKeys []int

		for k := range om.FromOldest() {
			visitedKeys = append(visitedKeys, k)

			// Insert before the first element and after the last element
			if k == 2 {
				om.InsertBefore(2, 1, "one") // Insert at beginning - won't be visited
			}
			if k == 4 {
				om.InsertAfter(4, 5, "five") // Insert at end - will be visited
			}
		}

		// Should visit original elements plus the element inserted at the end
		expectedKeys := []int{2, 3, 4, 5}
		assert.Equal(t, expectedKeys, visitedKeys, "iteration should visit original elements plus end insertion")

		// Verify final state shows insertions at beginning and end
		assertOrderedPairsEqual(t, om,
			[]int{1, 2, 3, 4, 5},
			[]string{"one", "two", "three", "four", "five"})
	})
}
