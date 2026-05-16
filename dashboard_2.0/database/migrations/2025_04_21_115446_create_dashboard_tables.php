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
        if (!Schema::hasTable('ic_master')) {
            Schema::create('ic_master', function (Blueprint $table) {
                $table->id();
                $table->integer('ic_id');
                $table->string('ic_name');
                $table->timestamps();
            });
        }

        if (!Schema::hasTable('policy_category')) {

            Schema::create('policy_category', function (Blueprint $table) {
                $table->id();
                $table->integer('category_id');
                $table->string('category_name');
                $table->timestamps();
            });
        }

        if (!Schema::hasTable('policy_type_master')) {
            Schema::create('policy_type_master', function (Blueprint $table) {
                $table->id();
                $table->integer('type_id');
                $table->string('policy_type_name')->nullable();
                $table->timestamps();
            });
        }

    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('policy_type_master');
        Schema::dropIfExists('policy_category');
        Schema::dropIfExists('ic_master');
    }
};
