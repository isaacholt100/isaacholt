import type { MDXComponents } from 'mdx/types'

export function useMDXComponents(components: MDXComponents): MDXComponents {
    return {
        pre: ({ children }) => (
            <pre className="border border-2 border-white rounded-2">
                {children}
            </pre>
        ),
        ...components,
    }
}