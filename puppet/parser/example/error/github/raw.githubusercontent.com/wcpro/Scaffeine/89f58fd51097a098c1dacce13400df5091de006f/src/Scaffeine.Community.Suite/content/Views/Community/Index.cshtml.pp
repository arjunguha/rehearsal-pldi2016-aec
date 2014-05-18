@{
    ViewBag.Title = "Index";
    Layout = "~/Views/Shared/_Layout.cshtml";
}
@section hero
{
    <div class="container" style="height: 200px; position:relative;">
        <h1>
            What's up</h1>
        <ul class="nav nav-tabs" style="position: absolute; left:0; bottom: -21px; width: 100%">
            <li class="active"><a href="#"><strong>Announcements</strong></a></li>
            <li><a href="#"><strong>Social Media</strong></a></li>
            <li><a href="#"><strong>Top Stories</strong></a></li>
            <li><a href="#"><strong>Knowledge Base</strong></a></li>
            <li><a href="#"><strong>Write an Article</strong></a></li>
        </ul>
    </div>
}
@section container{
    <div class="row-fluid" >
        <div class="span3">
            <h1>
                Social Media</h1>
        </div>
        <div class="span6">
            <h1>
                Announcements</h1>
        </div>
        <div class="span3 well">
            <h2>
                Featured Items</h2>
        </div>
    </div>
}
