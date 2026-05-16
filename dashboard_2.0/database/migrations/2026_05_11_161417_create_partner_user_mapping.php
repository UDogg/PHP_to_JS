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
        Schema::create('partner_user_mapping', function (Blueprint $table) {
            $table->id('partner_id');
            $table->string('partner_name');
            $table->string('user_id')->nullable();
            $table->string('theme_id')->nullable();
            $table->string('logo')->nullable();
            $table->string('favicon_icon')->nullable();
            $table->string('status')->default('Y');
            $table->timestamps();
            $table->softDeletes();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('partner_user_mapping');
    }
};
