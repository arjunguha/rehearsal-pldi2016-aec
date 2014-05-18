@using $rootnamespace$.Core.Common.Site
@section hero{
    <div class="hero-content">
        <h1>
            @Site.Instance.WebsiteName</h1>
        <p>
            Just another site built with ScaffR</p>
        <div class="actions">            
            <span class="nuget-badge">
                <code>PM&gt; Install-Package Scaffeine</code>
            </span>
        </div>
    </div>
}
<section id="social-buttons">
    <span class="watch">
        <a class="btn" href="http://www.github.com/wcpro/scaffr"><i class="icon-github"></i> Watch</a> 
        <span id="followers" class="count btn">1917</span> 
    </span>
    <span class="fork">
        <a class="btn" href="http://www.github.com/wcpro/scaffr"><i class="icon-github"></i> Fork</a> 
        <span id="followers" class="count btn">1917</span> 
    </span>
    <span class="follow">
        <a class="btn" href="http://www.facebook.com/scaffr">
            <i class="icon-facebook-sign"></i> Follow</a> 
        <span id="followers" class="count btn">1917</span> 
    </span>
    <span class="twitter">
        <a class="btn" href="http://www.twitter.com/scafffr"><i class="icon-twitter-sign"></i> Follow</a>
        <span id="followers" class="count btn">1917</span> 
    </span>
</section>
<section id="features">
    <div class="row">
        <div class="span4">
            <h3>
                <i class="icon-bolt"></i>Smart Code Generation
            </h3>
            ScaffR takes advantage of the latest Microsoft technologies to extend the functionality of Nuget.
        </div>
        <div class="span4">
            <h3>
                <i class="icon-copy"></i>A New Paradigm
            </h3>
            Easily design, build, and deploy perfect software. Learn the secrets to building
            highly-profitable software business using our proven techniques. <a href="#">Learn More</a>
        </div>
        <div class="span4">
            <h3>
                <i class="icon-magic"></i>Improved Productivity
            </h3>
            By utilizing our system, you will be more productive, and will build better software.
        </div>
    </div>
    <div class="row">
        <div class="span4">
            <h3>
                <i class="icon-copy"></i>Effective Code Reuse
            </h3>
            Our patterns for code reuse lower the overhead of developing really cool software
        </div>
        <div class="span4">
            <h3>
                <i class="icon-globe"></i>Production Ready
            </h3>
            Quickly generate software solutions that solve most business problems.  Want to offer recurring subscriptions to people to watch videos of cats?  Yeah, we can do that.
        </div>
        <div class="span4">
            <h3>
                <i class="icon-trophy"></i>Modular Architecture
            </h3>
            ScaffR is totally open source and always will be. Experts are available to assist
            you.
        </div>
    </div>
</section>
@section footer{
    <footer>
        <div class="row">
            <div class="span4">
                <h3>
                    Contact</h3>
                <ul class="icons">
                    <li><i class="icon-comment-alt"></i>Email</li>
                    <li><i class="icon-phone"></i>Phone</li>
                </ul>
            </div>
            <div class="span8">
                <h3>
                    License</h3>
                <p>
                    ScaffR is open-source and is subject to the super awesome license...
                </p>
            </div>
        </div>
    </footer>
}
