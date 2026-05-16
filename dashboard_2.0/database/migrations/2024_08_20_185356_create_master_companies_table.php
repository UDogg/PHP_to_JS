<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::create('master_companies', function (Blueprint $table) {
            $table->id("company_id");
            $table->string("company_name");
            $table->string("company_shortname");
            $table->string("health_alias");
            $table->string("motor_alias");
            $table->string("url");
            $table->string("logo");
            $table->string("is_renewal");
            $table->string("is_renewal_bike");
            $table->timestamps();
            $table->softDeletes();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('master_companies');
    }
};
