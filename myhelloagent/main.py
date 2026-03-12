import os
import sys
from openai import OpenAI

def main():
    # 1. Get the API key from your environment
    api_key = os.environ.get("OPENROUTER_API_KEY")
    
    if not api_key:
        print("Error: OPENROUTER_API_KEY not found in environment.")
        print("Please set it in your shell: export OPENROUTER_API_KEY='your-key-here'")
        sys.exit(1)

    # 2. Initialize the OpenAI client pointing to OpenRouter
    client = OpenAI(
        api_key=api_key,
        base_url="https://openrouter.ai/api/v1",
    )

    print("--- Simple Claude Agent (OpenRouter + OpenAI SDK) ---")
    print("Type 'exit' or 'quit' to stop.\n")

    while True:
        user_input = input("You: ")
        if user_input.lower() in ["exit", "quit"]:
            break

        try:
            # 3. Use the OpenAI chat completions format
            # Using OpenRouter model identifier
            response = client.chat.completions.create(
                model="deepseek/deepseek-v3.2",
                messages=[
                    {"role": "user", "content": user_input}
                ],
                # OpenRouter extra headers
                extra_headers={
                    "HTTP-Referer": "https://github.com/google/gemini-cli",
                    "X-Title": "My Hello Agent",
                }
            )

            # 4. Print the response
            agent_response = response.choices[0].message.content
            print(f"\nAgent: {agent_response}\n")

        except Exception as e:
            print(f"An error occurred: {e}")

if __name__ == "__main__":
    main()
