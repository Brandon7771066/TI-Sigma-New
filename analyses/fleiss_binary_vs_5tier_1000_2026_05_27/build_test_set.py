"""
Pass-77-B25 1000-statement test set builder.
- 500 random casual human speech from Tatoeba English corpus (CC-BY)
- 500 gold-labeled: 100 per category {T, F, I, MI, NA}
"""
import json
import random
import re

random.seed(20260527)

# === 500 casual sentences from Tatoeba ===
casual = []
with open("analyses/fleiss_binary_vs_5tier_1000_2026_05_27/eng.tsv") as f:
    for line in f:
        parts = line.rstrip("\n").split("\t")
        if len(parts) != 3:
            continue
        s = parts[2].strip()
        wc = len(s.split())
        if not (5 <= wc <= 18):
            continue
        if not re.search(r"^[A-Z]", s) or not s.endswith((".", "?", "!")):
            continue
        if re.search(r"[\u0080-\uFFFF]", s):  # non-ASCII
            continue
        if re.search(r"http|www\.|\.com|@", s.lower()):
            continue
        casual.append(s)

print(f"Filtered Tatoeba: {len(casual)} candidates")
random.shuffle(casual)
casual_sample = casual[:500]
print(f"Sampled: {len(casual_sample)} casual sentences")

# === 100 T (True) ===
T_templates = [
    "Water boils at 100 degrees Celsius at standard atmospheric pressure.",
    "The Earth orbits the Sun.",
    "Mount Everest is the tallest mountain above sea level.",
    "Humans have 23 pairs of chromosomes.",
    "Light travels faster than sound.",
    "The Great Wall of China is located in China.",
    "Oxygen is necessary for human respiration.",
    "World War II ended in 1945.",
    "The Pacific Ocean is larger than the Atlantic Ocean.",
    "Shakespeare wrote Hamlet.",
    "The capital of France is Paris.",
    "Mammals are warm-blooded animals.",
    "The Sun is a star.",
    "Antarctica is the coldest continent on Earth.",
    "The human body has 206 bones in adulthood.",
    "Lightning typically precedes the sound of thunder during a storm.",
    "Plants produce oxygen through photosynthesis.",
    "The Nile is one of the longest rivers in the world.",
    "Gold has the chemical symbol Au.",
    "The speed of light in vacuum is approximately 299,792 kilometers per second.",
]
# Math facts
for a in range(2, 22):
    T_templates.append(f"{a} plus {a} equals {2*a}.")
for a in range(3, 13):
    T_templates.append(f"{a} times {a} equals {a*a}.")
# Capital cities
caps = [("Germany","Berlin"),("Japan","Tokyo"),("Australia","Canberra"),("Egypt","Cairo"),
        ("Canada","Ottawa"),("Brazil","Brasilia"),("Russia","Moscow"),("Italy","Rome"),
        ("Spain","Madrid"),("India","New Delhi"),("Mexico","Mexico City"),("Greece","Athens"),
        ("Sweden","Stockholm"),("Norway","Oslo"),("Finland","Helsinki"),("Portugal","Lisbon"),
        ("Argentina","Buenos Aires"),("Thailand","Bangkok"),("Vietnam","Hanoi"),("Turkey","Ankara")]
for c,cap in caps:
    T_templates.append(f"The capital of {c} is {cap}.")
# Historical facts
T_templates += [
    "Neil Armstrong walked on the Moon in 1969.",
    "The Berlin Wall fell in 1989.",
    "Christopher Columbus reached the Americas in 1492.",
    "The American Civil War ended in 1865.",
    "Albert Einstein developed the theory of relativity.",
    "Marie Curie won Nobel Prizes in physics and chemistry.",
    "Charles Darwin wrote On the Origin of Species.",
    "Isaac Newton formulated the laws of motion.",
    "The Roman Empire eventually collapsed.",
    "Leonardo da Vinci painted the Mona Lisa.",
    "Beethoven composed nine symphonies.",
    "The Pyramids of Giza are located in Egypt.",
    "The Wright brothers built and flew the first successful airplane.",
    "Antibiotics can kill or inhibit the growth of bacteria.",
    "The chemical formula for water is H2O.",
    "Sodium chloride is the chemical name for table salt.",
    "DNA stands for deoxyribonucleic acid.",
    "Mercury is the closest planet to the Sun.",
    "Jupiter is the largest planet in our solar system.",
    "An equilateral triangle has three equal sides.",
    "A circle has 360 degrees.",
    "The square root of 144 is 12.",
    "Pi is approximately 3.14159.",
    "Hydrogen is the lightest element on the periodic table.",
    "A year on Earth has approximately 365 days.",
    "There are seven continents on Earth.",
    "The Amazon rainforest is located primarily in South America.",
    "The English alphabet has 26 letters.",
    "Carbon is an essential element in all known living organisms.",
    "The Eiffel Tower is located in Paris, France.",
    "Penguins are flightless birds.",
    "Sharks are fish, not mammals.",
    "The Atlantic Ocean separates Europe from the Americas.",
]
random.shuffle(T_templates)
T_props = T_templates[:100]

# === 100 F (False) ===
F_templates = [
    "Water boils at 50 degrees Celsius at standard atmospheric pressure.",
    "The Sun orbits the Earth.",
    "The capital of France is London.",
    "Humans have 12 pairs of chromosomes.",
    "Sound travels faster than light in a vacuum.",
    "Antarctica is the warmest continent on Earth.",
    "The Pacific Ocean is smaller than the Mediterranean Sea.",
    "Shakespeare wrote The Great Gatsby.",
    "Mount Everest is located in Brazil.",
    "Oxygen is a metal at room temperature.",
    "World War II ended in 1845.",
    "The Earth has three natural moons.",
    "Mammals are cold-blooded animals.",
    "Plants produce carbon dioxide through photosynthesis as their only gaseous output.",
    "The human heart has only one chamber.",
    "Gold has the chemical symbol Hy.",
    "The Nile river is located in Australia.",
    "Beethoven composed twenty-five symphonies.",
    "Pi is exactly equal to 4.",
    "There are fifteen continents on Earth.",
]
# Wrong math
for a in range(2, 22):
    F_templates.append(f"{a} plus {a} equals {2*a + 1}.")
for a in range(3, 13):
    F_templates.append(f"{a} times {a} equals {a*a + 5}.")
# Wrong capitals
wrong_caps = [("Germany","Lisbon"),("Japan","Seoul"),("Australia","Wellington"),("Egypt","Tehran"),
              ("Canada","Toronto"),("Brazil","Lima"),("Russia","Kiev"),("Italy","Madrid"),
              ("Spain","Lisbon"),("India","Karachi"),("Mexico","Bogota"),("Greece","Sofia"),
              ("Sweden","Oslo"),("Norway","Stockholm"),("Finland","Tallinn"),("Portugal","Madrid"),
              ("Argentina","Santiago"),("Thailand","Hanoi"),("Vietnam","Bangkok"),("Turkey","Athens")]
for c,cap in wrong_caps:
    F_templates.append(f"The capital of {c} is {cap}.")
F_templates += [
    "Neil Armstrong walked on Mars in 1969.",
    "The Berlin Wall fell in 1789.",
    "Christopher Columbus reached the Americas in 1992.",
    "The American Civil War ended in 1965.",
    "Albert Einstein developed the theory of evolution.",
    "Marie Curie won Nobel Prizes only in literature.",
    "Charles Darwin wrote Macbeth.",
    "Isaac Newton formulated the laws of thermodynamics.",
    "Leonardo da Vinci painted The Starry Night.",
    "The Pyramids of Giza are located in Norway.",
    "The Wright brothers built the first successful submarine.",
    "Antibiotics are effective against all viruses.",
    "The chemical formula for water is CO2.",
    "Sodium chloride is the chemical name for sugar.",
    "DNA stands for digital network adapter.",
    "Mercury is the largest planet in the solar system.",
    "Jupiter is the smallest planet in our solar system.",
    "An equilateral triangle has four equal sides.",
    "A circle has 540 degrees.",
    "The square root of 144 is 24.",
    "Hydrogen is the heaviest element on the periodic table.",
    "A year on Earth has approximately 100 days.",
    "The English alphabet has 50 letters.",
    "The Amazon rainforest is located primarily in Antarctica.",
    "Carbon is found nowhere in any known living organism.",
    "The Eiffel Tower is located in Tokyo, Japan.",
    "Penguins routinely fly long migration routes across the Pacific.",
    "Sharks are mammals, not fish.",
    "The Atlantic Ocean separates Asia from Africa.",
    "The human eye can naturally see X-rays.",
    "Cats are a species of reptile.",
    "Trees photosynthesize by absorbing nitrogen from soil and emitting helium.",
    "Stars are smaller than planets on average.",
]
random.shuffle(F_templates)
F_props = F_templates[:100]

# === 100 I (Indeterminate) ===
I_templates = [
    "It will rain in Tokyo exactly seven days from now.",
    "The number of cars on the road in Paris at this exact second is an even number.",
    "The next person to enter the Sydney Opera House will be left-handed.",
    "The President of the United States is currently sitting down.",
    "There is currently an odd number of birds within one mile of the Eiffel Tower.",
    "The price of gold will close higher than today's price exactly 90 days from now.",
    "Exactly 1,000,000 people are smiling somewhere in the world right now.",
    "The first child born tomorrow in Argentina will weigh more than 3 kilograms.",
    "An asteroid larger than 10 meters in diameter will pass within one lunar distance of Earth in the next 30 days.",
    "The next email you receive will contain the word 'thank'.",
    "There is at least one undiscovered species of insect in the Amazon rainforest.",
    "The total number of grains of sand on Bondi Beach right now is divisible by 7.",
    "A randomly chosen person in Beijing right now is wearing blue.",
    "The next dream you have will involve flying.",
    "There is an even number of fish currently in Lake Victoria.",
    "The atmospheric pressure at the summit of K2 right now is above the seasonal average.",
    "A person somewhere is humming a Beatles song at this very moment.",
    "There is currently a cat on a roof in Florence, Italy.",
    "The temperature in Reykjavik will exceed 15 degrees Celsius on Christmas Day next year.",
    "The next coin flipped anywhere on Earth will land on heads.",
    "An undiscovered moon larger than 100 meters across orbits Saturn.",
    "There exists somewhere in space an exoplanet harboring intelligent life.",
    "The total population of Antarctica right now is exactly 4,517.",
    "The first word spoken in your next phone call will start with the letter S.",
    "There is currently a four-leaf clover growing in Hyde Park.",
    "A specific unread book sits on the third shelf of a particular library in Reykjavik.",
    "The number of leaves currently on a particular maple tree in Vermont is prime.",
    "The exact mass of all blue whales currently alive is greater than 18 million kilograms.",
    "A flight currently airborne is carrying exactly one passenger named Theodore.",
    "Somewhere on Earth, a child is laughing right now.",
    "The next stranger you make eye contact with will be wearing glasses.",
    "There is at least one undelivered letter currently sitting in the New York City postal system addressed to a person named Maria.",
    "An ant currently walking across a sidewalk in Madrid will reach a crack in the next ten seconds.",
    "The Higgs boson decays into specific particles in a single given collision event no one has observed.",
    "A coin flipped in private by someone in Lagos one hour ago landed on tails.",
    "The number of stars visible to the naked eye from a specific rural location in Mongolia tonight will exceed 3,000.",
    "A particular grain of rice in a sealed container in Kyoto is touching exactly five other grains.",
    "There exists a particular drop of rainwater currently falling into Lake Geneva.",
    "The voltage at a specific power outlet in Helsinki right now is exactly 230.0 volts.",
    "Somewhere a stranger is thinking of the same word you are thinking of right now.",
    "The next car to pass a given intersection in Mumbai will be red.",
    "There is at least one undiscovered Roman coin buried within five kilometers of the Colosseum.",
    "The total weight of fish currently in the Yangtze river exceeds 50,000 metric tons.",
    "A specific bookstore in Berlin currently has exactly 12 customers inside.",
    "There is a fourth-grade student in Iowa right now solving a long-division problem.",
    "The wind speed at the top of the Burj Khalifa right now is greater than 30 kilometers per hour.",
    "There is at least one tea kettle currently whistling in Edinburgh.",
    "A randomly selected page from the next Wikipedia article you load will contain the word 'however'.",
    "There is an even number of clocks currently displaying 3:00 in London.",
    "The next sneeze that occurs anywhere on Earth will come from a man.",
    "A specific deer is currently drinking from a particular stream in Yellowstone National Park.",
    "There is an odd number of unsold loaves of bread currently in bakeries across Vienna.",
    "An ice cube melting in a glass in Cape Town will fully dissolve in less than four minutes.",
    "The next email sent worldwide will be sent from a device powered by a lithium battery.",
    "A specific frog is currently sitting on a lily pad in a pond in Louisiana.",
    "There is a marble currently resting at the bottom of a fountain in Rome.",
    "Right now, more people are awake in China than asleep in China.",
    "A bee currently flying somewhere in California will return to its hive within the next minute.",
    "The total number of red socks currently being worn in Greater London is divisible by 11.",
    "Somewhere a glass is currently being filled with orange juice.",
    "A specific oak leaf in Sherwood Forest will fall to the ground in the next 24 hours.",
    "The square of the number of unread emails in the inbox of a specific person in Cairo right now exceeds 10,000.",
    "There is a specific snowflake currently falling onto a rooftop in Vancouver.",
    "A bird somewhere is currently building a nest using string.",
    "The next car you see will have a license plate beginning with the letter T.",
    "There is currently at least one shoe missing its lace in the city of Toronto.",
    "An undiscovered species of deep-sea fish lives in the Mariana Trench.",
    "There exists at least one prime number greater than 10^100 that no human has yet considered.",
    "A specific photon emitted by a star in the Andromeda galaxy will reach Earth before 2030.",
    "A specific patient in a hospital in Lima currently has a resting heart rate of exactly 72.",
    "There is at least one violin currently being played somewhere in Paris.",
    "A particular cloud over the Atlantic Ocean will produce rain in the next 12 hours.",
    "The total amount of cash inside ATMs in Singapore right now exceeds 100 million Singapore dollars.",
    "Somewhere a dog is currently chasing its tail.",
    "There is at least one mosquito currently resting on a wall inside a building in Bangkok.",
    "The number of letters in the next sign you read will be a prime number.",
    "A specific snowflake landed on a specific tree branch in Norway one hour ago.",
    "The grand total of unfinished crossword puzzles currently in homes across the United States exceeds 5 million.",
    "There is a particular goldfish swimming clockwise in a particular bowl in Osaka.",
    "Somewhere a child is currently learning to ride a bicycle.",
    "An umbrella sits forgotten on a particular train car traveling through Switzerland.",
    "There is at least one fortune cookie containing the exact phrase 'A surprise awaits' currently being baked.",
    "A particular ant in a colony in Brazil will encounter another ant within the next five seconds.",
    "The total volume of coffee currently in mugs across Seattle exceeds 10,000 liters.",
    "There is a specific candle currently burning in a window in Reykjavik.",
    "The temperature at the exact center of Greenland right now is below minus 40 Celsius.",
    "A specific spider is currently weaving a web in a barn in Iowa.",
    "Right now, more shoes are tied than untied across all of New York City.",
    "There is at least one umbrella opened indoors in Tokyo right now.",
    "A randomly chosen page of a randomly chosen library book in Athens contains exactly 14 commas.",
    "There is currently an even number of running washing machines in Glasgow.",
    "Somewhere on Earth, an apple is falling from a tree at this exact moment.",
    "A specific drop of dew on a specific blade of grass in Surrey will evaporate before noon.",
    "The next person to win a major lottery will live in a city with population over 1 million.",
    "There is at least one violin string currently breaking somewhere in the world.",
    "A specific pencil in a school in Buenos Aires is currently being sharpened.",
    "Right now, somewhere in Africa, a giraffe is bending down to drink water.",
    "The total number of unread text messages on phones across Tokyo exceeds 50 million.",
    "There is at least one elderly person currently napping in a recliner in Madrid.",
    "The next bird call you hear will come from a sparrow.",
    "A particular cup of tea currently steeping somewhere in England will be drunk within 10 minutes.",
    "There is exactly one perfectly square chocolate bar currently on a shelf in Brussels.",
    "Right now, an even number of refrigerator doors are open across Paris.",
]
random.shuffle(I_templates)
I_props = I_templates[:100]

# === 100 MI (Meta-Indeterminate / Double-Tralse: paradoxes + self-contradictions + impossibilities) ===
MI_templates = [
    "This statement is false.",
    "The next sentence is true. The previous sentence is false.",
    "I am lying right now.",
    "There exists a married bachelor in this room.",
    "A four-sided triangle is on the table.",
    "The set of all sets that do not contain themselves contains itself.",
    "The barber shaves all and only those men who do not shave themselves; the barber shaves himself.",
    "A square circle is sitting on the chair.",
    "2 + 2 = 5 by definition of the standard arithmetical operators on the natural numbers.",
    "The largest prime number is currently being written on a chalkboard.",
    "A perfectly silent sound just played in the next room.",
    "An invisible visible object is on the floor.",
    "A completely empty container that is full of water sits on the desk.",
    "The current King of France is bald and there is currently no King of France.",
    "There is a number that is simultaneously equal to 7 and not equal to 7.",
    "An object that is both entirely red and entirely green at the same time and in the same respect is on the table.",
    "The number 3 is greater than itself.",
    "A bachelor who is currently married attended the dinner.",
    "There exists a real number that is greater than every real number.",
    "A circle whose every diameter is also a square's side appeared today.",
    "I know with absolute certainty that I know nothing with absolute certainty.",
    "This proposition has no truth value at all and is true.",
    "A complete and consistent first-order theory of arithmetic exists by Gödel's theorem.",
    "Today is both Monday and not Monday in the same sense at the same time.",
    "A function that is everywhere continuous and nowhere continuous exists.",
    "There is an integer between 4 and 5 exclusive.",
    "The set of all natural numbers is finite.",
    "A line segment of length 5 cm is longer than a line segment of length 7 cm of the same units.",
    "An object exists outside of all of existence.",
    "Some triangles have exactly two interior angles greater than 90 degrees each.",
    "The empty set contains exactly one element.",
    "A bachelor's wife is in the next room.",
    "There is a colorless red object in the corner.",
    "A perfectly straight curve was just drawn on the page.",
    "The last digit of pi was discovered yesterday.",
    "There is a sentence in English of exactly 100 words and exactly 50 words at the same time.",
    "A man taller than himself walked through the doorway.",
    "Every rule has exactly two exceptions including this one which has none.",
    "A married unmarried person attended the wedding.",
    "5 is both prime and even.",
    "A perfect contradiction is true.",
    "There is a non-circular circle on the wall.",
    "An odd even number was added to the column.",
    "The next paragraph contains only this sentence and exactly three other sentences.",
    "There exists a complete list of all true propositions including those not on this list.",
    "The set of all sets is itself a set in standard ZFC.",
    "I'm both alive and not alive in the same biological sense at the same time.",
    "A perfectly transparent opaque pane of glass was installed in the window.",
    "The number 7 is both prime and divisible by 2.",
    "I currently believe this exact sentence to be false.",
    "A perfectly straight zigzag line was drawn across the page.",
    "There exists a true sentence that asserts only its own falsity.",
    "The smallest positive real number is 0.0001.",
    "There is a set of size 3 that contains exactly 4 distinct elements.",
    "An equilateral triangle whose three angles sum to 200 degrees was constructed.",
    "There exists a square root of negative one in the real numbers.",
    "The next sentence is true and false simultaneously in the same respect: snow is white.",
    "A bachelor's daughter visited her father's wife.",
    "An immovable object collided with an unstoppable force in the lab.",
    "A blind person with full 20/20 vision read the book.",
    "There is a non-self-identical object on the shelf.",
    "Some object both exists and does not exist in the same sense at the same moment.",
    "A perfectly empty full glass was placed on the table.",
    "Every claim including this one has exactly one true counterexample which is this same claim.",
    "The proposition currently being asserted asserts only its own negation and is true.",
    "I know that I do not know the contents of this sentence which I have just read.",
    "A polygon with exactly two sides was drawn on the chalkboard.",
    "There exists an event that both occurred and did not occur at the same place and time in the same sense.",
    "A line segment is both finite in length and infinite in length at the same time.",
    "The chair I am sitting on is simultaneously made entirely of wood and entirely of glass with no parts in common.",
    "A solid liquid was placed in the beaker.",
    "There is a child who is older than her own father.",
    "The first ten digits of pi consist of exactly twelve different digits.",
    "An honest liar told the truth about being a perpetual liar.",
    "A circle with corners was traced on the floor.",
    "The number of digits in the largest prime is exactly fifteen.",
    "Some bachelors are widows.",
    "A perfectly round square was placed on the windowsill.",
    "I am currently both sitting and standing in the same posture at the same time.",
    "There exists a wholly invisible thing that is visible to the human eye.",
    "A child both older than 5 and younger than 5 years old attended class.",
    "All rules including this one have no exceptions whatsoever except for the present rule.",
    "There is a non-numerical number in the equation.",
    "An entirely silent loud sound was just made.",
    "A solid hollow sphere sits on the shelf.",
    "The proposition you are now reading is unreadable.",
    "There is a real number that is both rational and not rational.",
    "Some equilateral triangles are scalene.",
    "An entirely solid liquid filled the cup.",
    "There is a perfectly true false statement in this paragraph.",
    "A unicorn is both a real animal and not a real animal at the same time and in the same sense.",
    "Some odd numbers are prime; some prime numbers are not prime.",
    "Today exists both in the past and in the future and not in the present.",
    "A perfectly transparent brick wall blocks the view.",
    "I am the only person who exists, and there are other people in this room with me.",
    "A non-existent existing entity stands by the door.",
    "The square root of 25 is simultaneously 5 and not 5 in standard arithmetic.",
    "A husband who has never been married was invited.",
    "An object that is wholly here is also wholly somewhere else at the same time.",
    "There is a perfectly precise vague boundary.",
    "All generalizations are false including this one which is also true.",
    "A finite number greater than every finite number was computed.",
]
random.shuffle(MI_templates)
MI_props = MI_templates[:100]

# === 100 NA (Not Applicable / Category Mistake) ===
NA_templates = [
    "The number 7 smells distinctly of vanilla.",
    "Wednesday weighs more than Thursday.",
    "Justice has a measurable temperature in Celsius.",
    "The color blue is louder than the color red.",
    "Democracy tastes sweet on the tongue.",
    "The square root of 16 is purple.",
    "Friendship has a velocity of 30 meters per second.",
    "Forgiveness is approximately 4 centimeters long.",
    "Beauty is allergic to peanuts.",
    "The musical note middle C smells like lavender.",
    "The number pi is angry today.",
    "Honesty has feathers.",
    "Calculus is the brother of poetry.",
    "Geometry is left-handed.",
    "The Pythagorean theorem is sleepy.",
    "The integer 42 is married to the integer 17.",
    "Loyalty is approximately 2.3 kilograms in weight.",
    "Anger has a chemical formula.",
    "The Riemann hypothesis prefers vanilla ice cream.",
    "Thursday is taller than Friday.",
    "Compassion has an even number of legs.",
    "The set of all even numbers is jealous of the set of odd numbers.",
    "The Pythagorean theorem is shorter than Euclid's fifth postulate.",
    "Sincerity is bilingual.",
    "Grief has a melting point.",
    "Logic is a vegetarian.",
    "The number five enjoys jazz music.",
    "Curiosity has an electric charge.",
    "The empty set has a hometown.",
    "Algebra is approximately 6 feet tall.",
    "Tuesday is purple in flavor.",
    "Justice is measured in liters.",
    "The square root of 2 is married to the square root of 3.",
    "Patience has a chemical valence.",
    "The integer 100 is taller than the integer 50.",
    "Compassion runs on diesel fuel.",
    "The color green is older than the color red by two years.",
    "Mathematics smells like fresh-cut grass.",
    "Sadness is approximately 12 decibels.",
    "Logic has a favorite color.",
    "The number 7 is married.",
    "Honesty has a serial number ending in 4.",
    "The function f(x) = x^2 is afraid of spiders.",
    "Boredom has a wingspan of 4 meters.",
    "Algebra is a citizen of Spain.",
    "Friendship is divisible by 3.",
    "Wisdom has a phone number.",
    "Tuesday is allergic to wheat.",
    "The empty set has a favorite season.",
    "Trust runs at 60 hertz.",
    "The number 0 is in love with the number 1.",
    "Forgiveness measures 30 degrees Celsius.",
    "The Riemann hypothesis weighs 3 kilograms.",
    "Calculus is approximately 50 years old.",
    "Charity is left-handed.",
    "Geometry is married to algebra.",
    "Pi has a postal address in Rome.",
    "Generosity is approximately 4 ounces.",
    "The Pythagorean theorem is hungry.",
    "Logic is a Pisces.",
    "The integer 13 is unlucky in temperature.",
    "Compassion has a sour aftertaste.",
    "The function sine is afraid of heights.",
    "Justice has six legs.",
    "The set of natural numbers is bilingual.",
    "Honesty smells like wet dog.",
    "The number 4 is enrolled in college.",
    "Patience plays the trumpet.",
    "The complex plane is dating the real line.",
    "Trust is loud on Wednesdays.",
    "Wisdom is approximately 80 kilograms.",
    "The number 12 is from Belgium.",
    "Curiosity has a serial number printed on its side.",
    "Sadness has a melting point of 47 degrees.",
    "Algebra has a passport issued in 1999.",
    "The square root of 9 is currently asleep.",
    "Friendship has a chemical formula of C2H6O.",
    "Logic enjoys long walks on the beach.",
    "The empty set has hair.",
    "Calculus is approximately 1.7 meters tall.",
    "Justice has a favorite musical key.",
    "Honesty has a melting point.",
    "The number 6 enjoys watching documentaries.",
    "Compassion is fluent in Mandarin.",
    "The function tangent is married with two children.",
    "Geometry is afraid of dentists.",
    "The integer 21 is a vegetarian.",
    "Patience is exactly 4 grams heavy.",
    "Trust has a favorite breakfast cereal.",
    "Wisdom has eight legs and lives in caves.",
    "The set of prime numbers is currently traveling abroad.",
    "Algebra plays soccer on weekends.",
    "Loyalty is divisible by 7 evenly.",
    "Friendship has a serial number ending in 9.",
    "Logic prefers vacationing in the mountains.",
    "The Pythagorean theorem is approximately fifty kilograms.",
    "Justice is currently undergoing dental surgery.",
    "Sadness is fluent in French and German.",
    "The number 8 collects vintage stamps.",
    "Compassion has a postal code of 90210.",
    "Algebra is enrolled in a yoga class on Tuesdays.",
    "The Riemann hypothesis is currently looking for a roommate.",
]
random.shuffle(NA_templates)
NA_props = NA_templates[:100]

# Validate
assert len(T_props) == 100, len(T_props)
assert len(F_props) == 100, len(F_props)
assert len(I_props) == 100, len(I_props)
assert len(MI_props) == 100, len(MI_props)
assert len(NA_props) == 100, len(NA_props)
assert len(casual_sample) == 500, len(casual_sample)

# Build final test set
test_set = []
for i, text in enumerate(casual_sample):
    test_set.append({"id": f"CASUAL-{i:03d}", "gold": "CASUAL", "text": text})
for i, text in enumerate(T_props):
    test_set.append({"id": f"T-{i:03d}", "gold": "T", "text": text})
for i, text in enumerate(F_props):
    test_set.append({"id": f"F-{i:03d}", "gold": "F", "text": text})
for i, text in enumerate(I_props):
    test_set.append({"id": f"I-{i:03d}", "gold": "I", "text": text})
for i, text in enumerate(MI_props):
    test_set.append({"id": f"MI-{i:03d}", "gold": "MI", "text": text})
for i, text in enumerate(NA_props):
    test_set.append({"id": f"NA-{i:03d}", "gold": "NA", "text": text})

random.shuffle(test_set)

with open("analyses/fleiss_binary_vs_5tier_1000_2026_05_27/test_set.json", "w") as f:
    json.dump(test_set, f, indent=2)

print(f"Total test set: {len(test_set)} statements written to test_set.json")
print(f"Breakdown: 500 CASUAL + 100 T + 100 F + 100 I + 100 MI + 100 NA")
